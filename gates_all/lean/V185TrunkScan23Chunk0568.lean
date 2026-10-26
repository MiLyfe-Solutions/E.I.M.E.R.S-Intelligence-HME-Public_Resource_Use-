import V185TrunkScan23Chunk0567

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3358435 : List Nat := [1, 1, 1, 7, 2, 1, 2, 3, 1, 4]
def baseStart_3358435 : Nat := 118140960795 + 3358435 * 2 ^ 59
def prefixEnd_3358435 : Nat := 4983230072969 + 3 ^ 40 * 3358435 * 2
def baseEnd_3358435 : Nat := 574830467294224280439115

theorem tailTrace_3358435 : CollatzResearch.WordTrace tailWord_3358435 prefixEnd_3358435 574830467294224280439115 := by
  unfold tailWord_3358435
  simp only [CollatzResearch.WordTrace]
  refine ⟨122492187587971044878468759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81661458391980696585645839 122492187587971044878468759)
  ·
    refine ⟨183738281381956567317703139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122492187587971044878468759 183738281381956567317703139)
    ·
      refine ⟨275607422072934850976554709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183738281381956567317703139 275607422072934850976554709)
      ·
        refine ⟨6459548954834410569763001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 275607422072934850976554709 6459548954834410569763001)
        ·
          refine ⟨4844661716125807927322251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6459548954834410569763001 4844661716125807927322251)
          ·
            refine ⟨7266992574188711890983377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844661716125807927322251 7266992574188711890983377)
            ·
              refine ⟨5450244430641533918237533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7266992574188711890983377 5450244430641533918237533)
              ·
                refine ⟨2043841661490575219339075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5450244430641533918237533 2043841661490575219339075)
                ·
                  refine ⟨3065762492235862829008613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043841661490575219339075 3065762492235862829008613)
                  ·
                    refine ⟨574830467294224280439115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065762492235862829008613 574830467294224280439115)
                    ·
                      rfl

theorem cell23_3358435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 2, 3, 1, 4].length) (baseStart_3358435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358435 prefixEnd_3358435 := by exact prefixLift 3358435
  have htrace : WordTrace (prefixWord ++ tailWord_3358435) baseStart_3358435 baseEnd_3358435 := by
    simpa [prefixWord, tailWord_3358435, baseEnd_3358435] using wordTrace_append hprefix tailTrace_3358435
  have hstable : (prefixWord ++ tailWord_3358435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358435).length < 2 ^ (prefixWord ++ tailWord_3358435).sum := by decide
  have hdescent : baseEnd_3358435 < baseStart_3358435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358451 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 2, 3, 2]
def baseStart_3358451 : Nat := 118140960795 + 3358451 * 2 ^ 59
def prefixEnd_3358451 : Nat := 4983230072969 + 3 ^ 40 * 3358451 * 2
def baseEnd_3358451 : Nat := 1724499617573144778717271

theorem tailTrace_3358451 : CollatzResearch.WordTrace tailWord_3358451 prefixEnd_3358451 1724499617573144778717271 := by
  unfold tailWord_3358451
  simp only [CollatzResearch.WordTrace]
  refine ⟨122492771155913079611051207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81661847437275386407367471 122492771155913079611051207)
  ·
    refine ⟨183739156733869619416576811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122492771155913079611051207 183739156733869619416576811)
    ·
      refine ⟨275608735100804429124865217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183739156733869619416576811 275608735100804429124865217)
      ·
        refine ⟨206706551325603321843648913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275608735100804429124865217 206706551325603321843648913)
        ·
          refine ⟨155029913494202491382736685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206706551325603321843648913 155029913494202491382736685)
          ·
            refine ⟨58136217560325934268526257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155029913494202491382736685 58136217560325934268526257)
            ·
              refine ⟨43602163170244450701394693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58136217560325934268526257 43602163170244450701394693)
              ·
                refine ⟨8175405594420834506511505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43602163170244450701394693 8175405594420834506511505)
                ·
                  refine ⟨6131554195815625879883629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8175405594420834506511505 6131554195815625879883629)
                  ·
                    refine ⟨2299332823430859704956361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6131554195815625879883629 2299332823430859704956361)
                    ·
                      refine ⟨1724499617573144778717271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299332823430859704956361 1724499617573144778717271)
                      ·
                        rfl

theorem cell23_3358451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 2, 3, 2].length) (baseStart_3358451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358451 prefixEnd_3358451 := by exact prefixLift 3358451
  have htrace : WordTrace (prefixWord ++ tailWord_3358451) baseStart_3358451 baseEnd_3358451 := by
    simpa [prefixWord, tailWord_3358451, baseEnd_3358451] using wordTrace_append hprefix tailTrace_3358451
  have hstable : (prefixWord ++ tailWord_3358451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358451).length < 2 ^ (prefixWord ++ tailWord_3358451).sum := by decide
  have hdescent : baseEnd_3358451 < baseStart_3358451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358452 : List Nat := [2, 6, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_3358452 : Nat := 118140960795 + 3358452 * 2 ^ 59
def prefixEnd_3358452 : Nat := 4983230072969 + 3 ^ 40 * 3358452 * 2
def baseEnd_3358452 : Nat := 574833377017933091601589

theorem tailTrace_3358452 : CollatzResearch.WordTrace tailWord_3358452 prefixEnd_3358452 574833377017933091601589 := by
  unfold tailWord_3358452
  simp only [CollatzResearch.WordTrace]
  refine ⟨61246403814454728390918805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81661871752606304521225073 61246403814454728390918805)
  ·
    refine ⟨2870925178802565393324319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61246403814454728390918805 2870925178802565393324319)
    ·
      refine ⟨4306387768203848089986479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2870925178802565393324319 4306387768203848089986479)
      ·
        refine ⟨6459581652305772134979719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306387768203848089986479 6459581652305772134979719)
        ·
          refine ⟨9689372478458658202469579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459581652305772134979719 9689372478458658202469579)
          ·
            refine ⟨14534058717687987303704369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9689372478458658202469579 14534058717687987303704369)
            ·
              refine ⟨10900544038265990477778277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14534058717687987303704369 10900544038265990477778277)
              ·
                refine ⟨2043852007174873214583427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10900544038265990477778277 2043852007174873214583427)
                ·
                  refine ⟨3065778010762309821875141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2043852007174873214583427 3065778010762309821875141)
                  ·
                    refine ⟨574833377017933091601589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065778010762309821875141 574833377017933091601589)
                    ·
                      rfl

theorem cell23_3358452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_3358452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358452 prefixEnd_3358452 := by exact prefixLift 3358452
  have htrace : WordTrace (prefixWord ++ tailWord_3358452) baseStart_3358452 baseEnd_3358452 := by
    simpa [prefixWord, tailWord_3358452, baseEnd_3358452] using wordTrace_append hprefix tailTrace_3358452
  have hstable : (prefixWord ++ tailWord_3358452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358452).length < 2 ^ (prefixWord ++ tailWord_3358452).sum := by decide
  have hdescent : baseEnd_3358452 < baseStart_3358452 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358457 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 10]
def baseStart_3358457 : Nat := 118140960795 + 3358457 * 2 ^ 59
def prefixEnd_3358457 : Nat := 4983230072969 + 3 ^ 40 * 3358457 * 2
def baseEnd_3358457 : Nat := 574834232819023918414081

theorem tailTrace_3358457 : CollatzResearch.WordTrace tailWord_3358457 prefixEnd_3358457 574834232819023918414081 := by
  unfold tailWord_3358457
  simp only [CollatzResearch.WordTrace]
  refine ⟨122492989993891342635769625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81661993329260895090513083 122492989993891342635769625)
  ·
    refine ⟨91869742495418506976827219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122492989993891342635769625 91869742495418506976827219)
    ·
      refine ⟨137804613743127760465240829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91869742495418506976827219 137804613743127760465240829)
      ·
        refine ⟨51676730153672910174465311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137804613743127760465240829 51676730153672910174465311)
        ·
          refine ⟨77515095230509365261697967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51676730153672910174465311 77515095230509365261697967)
          ·
            refine ⟨116272642845764047892546951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77515095230509365261697967 116272642845764047892546951)
            ·
              refine ⟨174408964268646071838820427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116272642845764047892546951 174408964268646071838820427)
              ·
                refine ⟨261613446402969107758230641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174408964268646071838820427 261613446402969107758230641)
                ·
                  refine ⟨196210084802226830818672981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261613446402969107758230641 196210084802226830818672981)
                  ·
                    refine ⟨574834232819023918414081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 196210084802226830818672981 574834232819023918414081)
                    ·
                      rfl

theorem cell23_3358457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_3358457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358457 prefixEnd_3358457 := by exact prefixLift 3358457
  have htrace : WordTrace (prefixWord ++ tailWord_3358457) baseStart_3358457 baseEnd_3358457 := by
    simpa [prefixWord, tailWord_3358457, baseEnd_3358457] using wordTrace_append hprefix tailTrace_3358457
  have hstable : (prefixWord ++ tailWord_3358457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358457).length < 2 ^ (prefixWord ++ tailWord_3358457).sum := by decide
  have hdescent : baseEnd_3358457 < baseStart_3358457 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358501 : List Nat := [1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 5]
def baseStart_3358501 : Nat := 118140960795 + 3358501 * 2 ^ 59
def prefixEnd_3358501 : Nat := 4983230072969 + 3 ^ 40 * 3358501 * 2
def baseEnd_3358501 : Nat := 1724525291605869583092041

theorem tailTrace_3358501 : CollatzResearch.WordTrace tailWord_3358501 prefixEnd_3358501 1724525291605869583092041 := by
  unfold tailWord_3358501
  simp only [CollatzResearch.WordTrace]
  refine ⟨122494594805731938150371357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81663063203821292100247571 122494594805731938150371357)
  ·
    refine ⟨45935473052149476806389259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122494594805731938150371357 45935473052149476806389259)
    ·
      refine ⟨68903209578224215209583889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45935473052149476806389259 68903209578224215209583889)
      ·
        refine ⟨51677407183668161407187917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68903209578224215209583889 51677407183668161407187917)
        ·
          refine ⟨19379027693875560527695469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51677407183668161407187917 19379027693875560527695469)
          ·
            refine ⟨7267135385203335197885801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19379027693875560527695469 7267135385203335197885801)
            ·
              refine ⟨5450351538902501398414351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7267135385203335197885801 5450351538902501398414351)
              ·
                refine ⟨8175527308353752097621527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450351538902501398414351 8175527308353752097621527)
                ·
                  refine ⟨12263290962530628146432291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175527308353752097621527 12263290962530628146432291)
                  ·
                    refine ⟨18394936443795942219648437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12263290962530628146432291 18394936443795942219648437)
                    ·
                      refine ⟨1724525291605869583092041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18394936443795942219648437 1724525291605869583092041)
                      ·
                        rfl

theorem cell23_3358501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_3358501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358501 prefixEnd_3358501 := by exact prefixLift 3358501
  have htrace : WordTrace (prefixWord ++ tailWord_3358501) baseStart_3358501 baseEnd_3358501 := by
    simpa [prefixWord, tailWord_3358501, baseEnd_3358501] using wordTrace_append hprefix tailTrace_3358501
  have hstable : (prefixWord ++ tailWord_3358501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358501).length < 2 ^ (prefixWord ++ tailWord_3358501).sum := by decide
  have hdescent : baseEnd_3358501 < baseStart_3358501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358504 : List Nat := [2, 1, 5, 1, 1, 2, 11]
def baseStart_3358504 : Nat := 118140960795 + 3358504 * 2 ^ 59
def prefixEnd_3358504 : Nat := 4983230072969 + 3 ^ 40 * 3358504 * 2
def baseEnd_3358504 : Nat := 21290454716639914461167

theorem tailTrace_3358504 : CollatzResearch.WordTrace tailWord_3358504 prefixEnd_3358504 21290454716639914461167 := by
  unfold tailWord_3358504
  simp only [CollatzResearch.WordTrace]
  refine ⟨61247352112360534831365283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81663136149814046441820377 61247352112360534831365283)
  ·
    refine ⟨91871028168540802247047925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61247352112360534831365283 91871028168540802247047925)
    ·
      refine ⟨8612908890800700210660743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91871028168540802247047925 8612908890800700210660743)
      ·
        refine ⟨12919363336201050315991115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8612908890800700210660743 12919363336201050315991115)
        ·
          refine ⟨19379045004301575473986673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12919363336201050315991115 19379045004301575473986673)
          ·
            refine ⟨14534283753226181605490005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19379045004301575473986673 14534283753226181605490005)
            ·
              refine ⟨21290454716639914461167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14534283753226181605490005 21290454716639914461167)
              ·
                rfl

theorem cell23_3358504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 11].length) (baseStart_3358504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358504 prefixEnd_3358504 := by exact prefixLift 3358504
  have htrace : WordTrace (prefixWord ++ tailWord_3358504) baseStart_3358504 baseEnd_3358504 := by
    simpa [prefixWord, tailWord_3358504, baseEnd_3358504] using wordTrace_append hprefix tailTrace_3358504
  have hstable : (prefixWord ++ tailWord_3358504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358504).length < 2 ^ (prefixWord ++ tailWord_3358504).sum := by decide
  have hdescent : baseEnd_3358504 < baseStart_3358504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358518 : List Nat := [5, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5]
def baseStart_3358518 : Nat := 118140960795 + 3358518 * 2 ^ 59
def prefixEnd_3358518 : Nat := 4983230072969 + 3 ^ 40 * 3358518 * 2
def baseEnd_3358518 : Nat := 1724534020776996016579463

theorem tailTrace_3358518 : CollatzResearch.WordTrace tailWord_3358518 prefixEnd_3358518 1724534020776996016579463 := by
  unfold tailWord_3358518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7655950927916896878358763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81663476564446900035826805 7655950927916896878358763)
  ·
    refine ⟨11483926391875345317538145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7655950927916896878358763 11483926391875345317538145)
    ·
      refine ⟨8612944793906508988153609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11483926391875345317538145 8612944793906508988153609)
      ·
        refine ⟨6459708595429881741115207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8612944793906508988153609 6459708595429881741115207)
        ·
          refine ⟨9689562893144822611672811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459708595429881741115207 9689562893144822611672811)
          ·
            refine ⟨14534344339717233917509217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9689562893144822611672811 14534344339717233917509217)
            ·
              refine ⟨10900758254787925438131913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14534344339717233917509217 10900758254787925438131913)
              ·
                refine ⟨8175568691090944078598935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10900758254787925438131913 8175568691090944078598935)
                ·
                  refine ⟨12263353036636416117898403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175568691090944078598935 12263353036636416117898403)
                  ·
                    refine ⟨18395029554954624176847605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12263353036636416117898403 18395029554954624176847605)
                    ·
                      refine ⟨1724534020776996016579463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18395029554954624176847605 1724534020776996016579463)
                      ·
                        rfl

theorem cell23_3358518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_3358518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358518 prefixEnd_3358518 := by exact prefixLift 3358518
  have htrace : WordTrace (prefixWord ++ tailWord_3358518) baseStart_3358518 baseEnd_3358518 := by
    simpa [prefixWord, tailWord_3358518, baseEnd_3358518] using wordTrace_append hprefix tailTrace_3358518
  have hstable : (prefixWord ++ tailWord_3358518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358518).length < 2 ^ (prefixWord ++ tailWord_3358518).sum := by decide
  have hdescent : baseEnd_3358518 < baseStart_3358518 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358525 : List Nat := [1, 4, 1, 4, 1, 1, 4, 1, 2, 4]
def baseStart_3358525 : Nat := 118140960795 + 3358525 * 2 ^ 59
def prefixEnd_3358525 : Nat := 4983230072969 + 3 ^ 40 * 3358525 * 2
def baseEnd_3358525 : Nat := 574845871713859163063977

theorem tailTrace_3358525 : CollatzResearch.WordTrace tailWord_3358525 prefixEnd_3358525 574845871713859163063977 := by
  unfold tailWord_3358525
  simp only [CollatzResearch.WordTrace]
  refine ⟨122495470157644990249245029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81663646771763326832830019 122495470157644990249245029)
  ·
    refine ⟨22967900654558435671733443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122495470157644990249245029 22967900654558435671733443)
    ·
      refine ⟨34451850981837653507600165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22967900654558435671733443 34451850981837653507600165)
      ·
        refine ⟨6459722059094560032675031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34451850981837653507600165 6459722059094560032675031)
        ·
          refine ⟨9689583088641840049012547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6459722059094560032675031 9689583088641840049012547)
          ·
            refine ⟨14534374632962760073518821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9689583088641840049012547 14534374632962760073518821)
            ·
              refine ⟨2725195243680517513784779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14534374632962760073518821 2725195243680517513784779)
              ·
                refine ⟨4087792865520776270677169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725195243680517513784779 4087792865520776270677169)
                ·
                  refine ⟨3065844649140582203007877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4087792865520776270677169 3065844649140582203007877)
                  ·
                    refine ⟨574845871713859163063977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3065844649140582203007877 574845871713859163063977)
                    ·
                      rfl

theorem cell23_3358525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_3358525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358525 prefixEnd_3358525 := by exact prefixLift 3358525
  have htrace : WordTrace (prefixWord ++ tailWord_3358525) baseStart_3358525 baseEnd_3358525 := by
    simpa [prefixWord, tailWord_3358525, baseEnd_3358525] using wordTrace_append hprefix tailTrace_3358525
  have hstable : (prefixWord ++ tailWord_3358525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358525).length < 2 ^ (prefixWord ++ tailWord_3358525).sum := by decide
  have hdescent : baseEnd_3358525 < baseStart_3358525 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358548 : List Nat := [2, 4, 1, 1, 3, 2, 1, 2, 1, 3, 3]
def baseStart_3358548 : Nat := 118140960795 + 3358548 * 2 ^ 59
def prefixEnd_3358548 : Nat := 4983230072969 + 3 ^ 40 * 3358548 * 2
def baseEnd_3358548 : Nat := 1724549425196630899204325

theorem tailTrace_3358548 : CollatzResearch.WordTrace tailWord_3358548 prefixEnd_3358548 1724549425196630899204325 := by
  unfold tailWord_3358548
  simp only [CollatzResearch.WordTrace]
  refine ⟨61248154518280832588666149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81664206024374443451554865 61248154518280832588666149)
  ·
    refine ⟨11484028972177656110374903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61248154518280832588666149 11484028972177656110374903)
    ·
      refine ⟨17226043458266484165562355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11484028972177656110374903 17226043458266484165562355)
      ·
        refine ⟨25839065187399726248343533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17226043458266484165562355 25839065187399726248343533)
        ·
          refine ⟨9689649445274897343128825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25839065187399726248343533 9689649445274897343128825)
          ·
            refine ⟨7267237083956173007346619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9689649445274897343128825 7267237083956173007346619)
            ·
              refine ⟨10900855625934259511019929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267237083956173007346619 10900855625934259511019929)
              ·
                refine ⟨8175641719450694633264947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10900855625934259511019929 8175641719450694633264947)
                ·
                  refine ⟨12263462579176041949897421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8175641719450694633264947 12263462579176041949897421)
                  ·
                    refine ⟨4598798467191015731211533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12263462579176041949897421 4598798467191015731211533)
                    ·
                      refine ⟨1724549425196630899204325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4598798467191015731211533 1724549425196630899204325)
                      ·
                        rfl

theorem cell23_3358548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 2, 1, 3, 3].length) (baseStart_3358548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358548 prefixEnd_3358548 := by exact prefixLift 3358548
  have htrace : WordTrace (prefixWord ++ tailWord_3358548) baseStart_3358548 baseEnd_3358548 := by
    simpa [prefixWord, tailWord_3358548, baseEnd_3358548] using wordTrace_append hprefix tailTrace_3358548
  have hstable : (prefixWord ++ tailWord_3358548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358548).length < 2 ^ (prefixWord ++ tailWord_3358548).sum := by decide
  have hdescent : baseEnd_3358548 < baseStart_3358548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358571 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 5, 4, 2]
def baseStart_3358571 : Nat := 118140960795 + 3358571 * 2 ^ 59
def prefixEnd_3358571 : Nat := 4983230072969 + 3 ^ 40 * 3358571 * 2
def baseEnd_3358571 : Nat := 1724561235251684309216719

theorem tailTrace_3358571 : CollatzResearch.WordTrace tailWord_3358571 prefixEnd_3358571 1724561235251684309216719 := by
  unfold tailWord_3358571
  simp only [CollatzResearch.WordTrace]
  refine ⟨122497147915478340105419567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81664765276985560070279711 122497147915478340105419567)
  ·
    refine ⟨183745721873217510158129351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122497147915478340105419567 183745721873217510158129351)
    ·
      refine ⟨275618582809826265237194027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183745721873217510158129351 275618582809826265237194027)
      ·
        refine ⟨413427874214739397855791041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275618582809826265237194027 413427874214739397855791041)
        ·
          refine ⟨310070905661054548391843281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413427874214739397855791041 310070905661054548391843281)
          ·
            refine ⟨232553179245790911293882461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310070905661054548391843281 232553179245790911293882461)
            ·
              refine ⟨87207442217171591735205923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232553179245790911293882461 87207442217171591735205923)
              ·
                refine ⟨130811163325757387602808885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87207442217171591735205923 130811163325757387602808885)
                ·
                  refine ⟨12263546561789755087763333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130811163325757387602808885 12263546561789755087763333)
                  ·
                    refine ⟨2299414980335579078955625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12263546561789755087763333 2299414980335579078955625)
                    ·
                      refine ⟨1724561235251684309216719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299414980335579078955625 1724561235251684309216719)
                      ·
                        rfl

theorem cell23_3358571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 5, 4, 2].length) (baseStart_3358571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358571 prefixEnd_3358571 := by exact prefixLift 3358571
  have htrace : WordTrace (prefixWord ++ tailWord_3358571) baseStart_3358571 baseEnd_3358571 := by
    simpa [prefixWord, tailWord_3358571, baseEnd_3358571] using wordTrace_append hprefix tailTrace_3358571
  have hstable : (prefixWord ++ tailWord_3358571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358571).length < 2 ^ (prefixWord ++ tailWord_3358571).sum := by decide
  have hdescent : baseEnd_3358571 < baseStart_3358571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358581 : List Nat := [1, 3, 4, 1, 1, 1, 3, 1, 2, 6]
def baseStart_3358581 : Nat := 118140960795 + 3358581 * 2 ^ 59
def prefixEnd_3358581 : Nat := 4983230072969 + 3 ^ 40 * 3358581 * 2
def baseEnd_3358581 : Nat := 574855456686076423363891

theorem tailTrace_3358581 : CollatzResearch.WordTrace tailWord_3358581 prefixEnd_3358581 574855456686076423363891 := by
  unfold tailWord_3358581
  simp only [CollatzResearch.WordTrace]
  refine ⟨122497512645442111813283597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81665008430294741208855731 122497512645442111813283597)
  ·
    refine ⟨45936567242040791929981349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122497512645442111813283597 45936567242040791929981349)
    ·
      refine ⟨8613106357882648486871503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45936567242040791929981349 8613106357882648486871503)
      ·
        refine ⟨12919659536823972730307255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8613106357882648486871503 12919659536823972730307255)
        ·
          refine ⟨19379489305235959095460883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12919659536823972730307255 19379489305235959095460883)
          ·
            refine ⟨29069233957853938643191325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19379489305235959095460883 29069233957853938643191325)
            ·
              refine ⟨10900962734195226991196747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29069233957853938643191325 10900962734195226991196747)
              ·
                refine ⟨16351444101292840486795121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10900962734195226991196747 16351444101292840486795121)
                ·
                  refine ⟨12263583075969630365096341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16351444101292840486795121 12263583075969630365096341)
                  ·
                    refine ⟨574855456686076423363891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12263583075969630365096341 574855456686076423363891)
                    ·
                      rfl

theorem cell23_3358581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_3358581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358581 prefixEnd_3358581 := by exact prefixLift 3358581
  have htrace : WordTrace (prefixWord ++ tailWord_3358581) baseStart_3358581 baseEnd_3358581 := by
    simpa [prefixWord, tailWord_3358581, baseEnd_3358581] using wordTrace_append hprefix tailTrace_3358581
  have hstable : (prefixWord ++ tailWord_3358581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358581).length < 2 ^ (prefixWord ++ tailWord_3358581).sum := by decide
  have hdescent : baseEnd_3358581 < baseStart_3358581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358588 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_3358588 : Nat := 118140960795 + 3358588 * 2 ^ 59
def prefixEnd_3358588 : Nat := 4983230072969 + 3 ^ 40 * 3358588 * 2
def baseEnd_3358588 : Nat := 1724569964422810742704141

theorem tailTrace_3358588 : CollatzResearch.WordTrace tailWord_3358588 prefixEnd_3358588 1724569964422810742704141 := by
  unfold tailWord_3358588
  simp only [CollatzResearch.WordTrace]
  refine ⟨61248883978208376004394209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81665178637611168005858945 61248883978208376004394209)
  ·
    refine ⟨45936662983656282003295657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61248883978208376004394209 45936662983656282003295657)
    ·
      refine ⟨34452497237742211502471743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45936662983656282003295657 34452497237742211502471743)
      ·
        refine ⟨51678745856613317253707615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34452497237742211502471743 51678745856613317253707615)
        ·
          refine ⟨77518118784919975880561423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51678745856613317253707615 77518118784919975880561423)
          ·
            refine ⟨116277178177379963820842135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77518118784919975880561423 116277178177379963820842135)
            ·
              refine ⟨174415767266069945731263203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116277178177379963820842135 174415767266069945731263203)
              ·
                refine ⟨261623650899104918596894805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174415767266069945731263203 261623650899104918596894805)
                ·
                  refine ⟨3065902158973885764807361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 261623650899104918596894805 3065902158973885764807361)
                  ·
                    refine ⟨2299426619230414323605521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3065902158973885764807361 2299426619230414323605521)
                    ·
                      refine ⟨1724569964422810742704141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299426619230414323605521 1724569964422810742704141)
                      ·
                        rfl

theorem cell23_3358588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_3358588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358588 prefixEnd_3358588 := by exact prefixLift 3358588
  have htrace : WordTrace (prefixWord ++ tailWord_3358588) baseStart_3358588 baseEnd_3358588 := by
    simpa [prefixWord, tailWord_3358588, baseEnd_3358588] using wordTrace_append hprefix tailTrace_3358588
  have hstable : (prefixWord ++ tailWord_3358588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358588).length < 2 ^ (prefixWord ++ tailWord_3358588).sum := by decide
  have hdescent : baseEnd_3358588 < baseStart_3358588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358604 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_3358604 : Nat := 118140960795 + 3358604 * 2 ^ 59
def prefixEnd_3358604 : Nat := 4983230072969 + 3 ^ 40 * 3358604 * 2
def baseEnd_3358604 : Nat := 1724578180113282680104067

theorem tailTrace_3358604 : CollatzResearch.WordTrace tailWord_3358604 prefixEnd_3358604 1724578180113282680104067 := by
  unfold tailWord_3358604
  simp only [CollatzResearch.WordTrace]
  refine ⟨61249175762179393370685433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81665567682905857827580577 61249175762179393370685433)
  ·
    refine ⟨45936881821634545028014075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61249175762179393370685433 45936881821634545028014075)
    ·
      refine ⟨68905322732451817542021113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45936881821634545028014075 68905322732451817542021113)
      ·
        refine ⟨51678992049338863156515835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68905322732451817542021113 51678992049338863156515835)
        ·
          refine ⟨77518488074008294734773753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51678992049338863156515835 77518488074008294734773753)
          ·
            refine ⟨58138866055506221051080315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77518488074008294734773753 58138866055506221051080315)
            ·
              refine ⟨87208299083259331576620473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58138866055506221051080315 87208299083259331576620473)
              ·
                refine ⟨65406224312444498682465355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87208299083259331576620473 65406224312444498682465355)
                ·
                  refine ⟨98109336468666748023698033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65406224312444498682465355 98109336468666748023698033)
                  ·
                    refine ⟨73582002351500061017773525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98109336468666748023698033 73582002351500061017773525)
                    ·
                      refine ⟨1724578180113282680104067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73582002351500061017773525 1724578180113282680104067)
                      ·
                        rfl

theorem cell23_3358604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_3358604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358604 prefixEnd_3358604 := by exact prefixLift 3358604
  have htrace : WordTrace (prefixWord ++ tailWord_3358604) baseStart_3358604 baseEnd_3358604 := by
    simpa [prefixWord, tailWord_3358604, baseEnd_3358604] using wordTrace_append hprefix tailTrace_3358604
  have hstable : (prefixWord ++ tailWord_3358604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358604).length < 2 ^ (prefixWord ++ tailWord_3358604).sum := by decide
  have hdescent : baseEnd_3358604 < baseStart_3358604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358628 : List Nat := [2, 3, 1, 2, 1, 3, 2, 4, 5]
def baseStart_3358628 : Nat := 118140960795 + 3358628 * 2 ^ 59
def prefixEnd_3358628 : Nat := 4983230072969 + 3 ^ 40 * 3358628 * 2
def baseEnd_3358628 : Nat := 191621167072110065133773

theorem tailTrace_3358628 : CollatzResearch.WordTrace tailWord_3358628 prefixEnd_3358628 191621167072110065133773 := by
  unfold tailWord_3358628
  simp only [CollatzResearch.WordTrace]
  refine ⟨61249613438135919420122269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81666151250847892560163025 61249613438135919420122269)
  ·
    refine ⟨22968605039300969782545851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61249613438135919420122269 22968605039300969782545851)
    ·
      refine ⟨34452907558951454673818777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22968605039300969782545851 34452907558951454673818777)
      ·
        refine ⟨25839680669213591005364083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34452907558951454673818777 25839680669213591005364083)
        ·
          refine ⟨38759521003820386508046125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25839680669213591005364083 38759521003820386508046125)
          ·
            refine ⟨14534820376432644940517297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38759521003820386508046125 14534820376432644940517297)
            ·
              refine ⟨10901115282324483705387973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14534820376432644940517297 10901115282324483705387973)
              ·
                refine ⟨2043959115435840694760245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10901115282324483705387973 2043959115435840694760245)
                ·
                  refine ⟨191621167072110065133773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2043959115435840694760245 191621167072110065133773)
                  ·
                    rfl

theorem cell23_3358628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_3358628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358628 prefixEnd_3358628 := by exact prefixLift 3358628
  have htrace : WordTrace (prefixWord ++ tailWord_3358628) baseStart_3358628 baseEnd_3358628 := by
    simpa [prefixWord, tailWord_3358628, baseEnd_3358628] using wordTrace_append hprefix tailTrace_3358628
  have hstable : (prefixWord ++ tailWord_3358628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358628).length < 2 ^ (prefixWord ++ tailWord_3358628).sum := by decide
  have hdescent : baseEnd_3358628 < baseStart_3358628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358641 : List Nat := [1, 2, 2, 4, 2, 1, 1, 2, 1, 7]
def baseStart_3358641 : Nat := 118140960795 + 3358641 * 2 ^ 59
def prefixEnd_3358641 : Nat := 4983230072969 + 3 ^ 40 * 3358641 * 2
def baseEnd_3358641 : Nat := 574865726299166345113799

theorem tailTrace_3358641 : CollatzResearch.WordTrace tailWord_3358641 prefixEnd_3358641 574865726299166345113799 := by
  unfold tailWord_3358641
  simp only [CollatzResearch.WordTrace]
  refine ⟨122499701025224742060467777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81666467350149828040311851 122499701025224742060467777)
  ·
    refine ⟨91874775768918556545350833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122499701025224742060467777 91874775768918556545350833)
    ·
      refine ⟨68906081826688917409013125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91874775768918556545350833 68906081826688917409013125)
      ·
        refine ⟨12919890342504172014189961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68906081826688917409013125 12919890342504172014189961)
        ·
          refine ⟨9689917756878129010642471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12919890342504172014189961 9689917756878129010642471)
          ·
            refine ⟨14534876635317193515963707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9689917756878129010642471 14534876635317193515963707)
            ·
              refine ⟨21802314952975790273945561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14534876635317193515963707 21802314952975790273945561)
              ·
                refine ⟨16351736214731842705459171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21802314952975790273945561 16351736214731842705459171)
                ·
                  refine ⟨24527604322097764058188757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16351736214731842705459171 24527604322097764058188757)
                  ·
                    refine ⟨574865726299166345113799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24527604322097764058188757 574865726299166345113799)
                    ·
                      rfl

theorem cell23_3358641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 2, 1, 7].length) (baseStart_3358641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358641 prefixEnd_3358641 := by exact prefixLift 3358641
  have htrace : WordTrace (prefixWord ++ tailWord_3358641) baseStart_3358641 baseEnd_3358641 := by
    simpa [prefixWord, tailWord_3358641, baseEnd_3358641] using wordTrace_append hprefix tailTrace_3358641
  have hstable : (prefixWord ++ tailWord_3358641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358641).length < 2 ^ (prefixWord ++ tailWord_3358641).sum := by decide
  have hdescent : baseEnd_3358641 < baseStart_3358641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358698 : List Nat := [3, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_3358698 : Nat := 118140960795 + 3358698 * 2 ^ 59
def prefixEnd_3358698 : Nat := 4983230072969 + 3 ^ 40 * 3358698 * 2
def baseEnd_3358698 : Nat := 1724626447294805312328635

theorem tailTrace_3358698 : CollatzResearch.WordTrace tailWord_3358698 prefixEnd_3358698 1724626447294805312328635 := by
  unfold tailWord_3358698
  simp only [CollatzResearch.WordTrace]
  refine ⟨30625444996504560198823187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81667853324012160530195165 30625444996504560198823187)
  ·
    refine ⟨45938167494756840298234781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30625444996504560198823187 45938167494756840298234781)
    ·
      refine ⟨17226812810533815111838043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45938167494756840298234781 17226812810533815111838043)
      ·
        refine ⟨25840219215800722667757065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17226812810533815111838043 25840219215800722667757065)
        ·
          refine ⟨19380164411850542000817799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25840219215800722667757065 19380164411850542000817799)
          ·
            refine ⟨29070246617775813001226699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19380164411850542000817799 29070246617775813001226699)
            ·
              refine ⟨43605369926663719501840049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29070246617775813001226699 43605369926663719501840049)
              ·
                refine ⟨32704027444997789626380037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43605369926663719501840049 32704027444997789626380037)
                ·
                  refine ⟨6132005145937085554946257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32704027444997789626380037 6132005145937085554946257)
                  ·
                    refine ⟨4599003859452814166209693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6132005145937085554946257 4599003859452814166209693)
                    ·
                      refine ⟨1724626447294805312328635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599003859452814166209693 1724626447294805312328635)
                      ·
                        rfl

theorem cell23_3358698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_3358698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358698 prefixEnd_3358698 := by exact prefixLift 3358698
  have htrace : WordTrace (prefixWord ++ tailWord_3358698) baseStart_3358698 baseEnd_3358698 := by
    simpa [prefixWord, tailWord_3358698, baseEnd_3358698] using wordTrace_append hprefix tailTrace_3358698
  have hstable : (prefixWord ++ tailWord_3358698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358698).length < 2 ^ (prefixWord ++ tailWord_3358698).sum := by decide
  have hdescent : baseEnd_3358698 < baseStart_3358698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358748 : List Nat := [2, 2, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_3358748 : Nat := 118140960795 + 3358748 * 2 ^ 59
def prefixEnd_3358748 : Nat := 4983230072969 + 3 ^ 40 * 3358748 * 2
def baseEnd_3358748 : Nat := 574884040442510038901135

theorem tailTrace_3358748 : CollatzResearch.WordTrace tailWord_3358748 prefixEnd_3358748 574884040442510038901135 := by
  unfold tailWord_3358748
  simp only [CollatzResearch.WordTrace]
  refine ⟨61251801817918549667306449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81669069090558066223075265 61251801817918549667306449)
  ·
    refine ⟨45938851363438912250479837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61251801817918549667306449 45938851363438912250479837)
    ·
      refine ⟨17227069261289592093929939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45938851363438912250479837 17227069261289592093929939)
      ·
        refine ⟨25840603891934388140894909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17227069261289592093929939 25840603891934388140894909)
        ·
          refine ⟨9690226459475395552835591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25840603891934388140894909 9690226459475395552835591)
          ·
            refine ⟨14535339689213093329253387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9690226459475395552835591 14535339689213093329253387)
            ·
              refine ⟨21803009533819639993880081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14535339689213093329253387 21803009533819639993880081)
              ·
                refine ⟨16352257150364729995410061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21803009533819639993880081 16352257150364729995410061)
                ·
                  refine ⟨6132096431386773748278773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16352257150364729995410061 6132096431386773748278773)
                  ·
                    refine ⟨574884040442510038901135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6132096431386773748278773 574884040442510038901135)
                    ·
                      rfl

theorem cell23_3358748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_3358748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358748 prefixEnd_3358748 := by exact prefixLift 3358748
  have htrace : WordTrace (prefixWord ++ tailWord_3358748) baseStart_3358748 baseEnd_3358748 := by
    simpa [prefixWord, tailWord_3358748, baseEnd_3358748] using wordTrace_append hprefix tailTrace_3358748
  have hstable : (prefixWord ++ tailWord_3358748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358748).length < 2 ^ (prefixWord ++ tailWord_3358748).sum := by decide
  have hdescent : baseEnd_3358748 < baseStart_3358748 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358762 : List Nat := [3, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_3358762 : Nat := 118140960795 + 3358762 * 2 ^ 59
def prefixEnd_3358762 : Nat := 4983230072969 + 3 ^ 40 * 3358762 * 2
def baseEnd_3358762 : Nat := 1724659310056693061928341

theorem tailTrace_3358762 : CollatzResearch.WordTrace tailWord_3358762 prefixEnd_3358762 1724659310056693061928341 := by
  unfold tailWord_3358762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30626028564446594931405635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81669409505190919817081693 30626028564446594931405635)
  ·
    refine ⟨45939042846669892397108453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30626028564446594931405635 45939042846669892397108453)
    ·
      refine ⟨8613570533750604824457835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45939042846669892397108453 8613570533750604824457835)
      ·
        refine ⟨12920355800625907236686753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8613570533750604824457835 12920355800625907236686753)
        ·
          refine ⟨9690266850469430427515065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12920355800625907236686753 9690266850469430427515065)
          ·
            refine ⟨7267700137852072820636299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9690266850469430427515065 7267700137852072820636299)
            ·
              refine ⟨10901550206778109230954449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267700137852072820636299 10901550206778109230954449)
              ·
                refine ⟨8176162655083581923215837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10901550206778109230954449 8176162655083581923215837)
                ·
                  refine ⟨3066060995656343221205939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8176162655083581923215837 3066060995656343221205939)
                  ·
                    refine ⟨4599091493484514831808909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3066060995656343221205939 4599091493484514831808909)
                    ·
                      refine ⟨1724659310056693061928341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599091493484514831808909 1724659310056693061928341)
                      ·
                        rfl

theorem cell23_3358762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_3358762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358762 prefixEnd_3358762 := by exact prefixLift 3358762
  have htrace : WordTrace (prefixWord ++ tailWord_3358762) baseStart_3358762 baseEnd_3358762 := by
    simpa [prefixWord, tailWord_3358762, baseEnd_3358762] using wordTrace_append hprefix tailTrace_3358762
  have hstable : (prefixWord ++ tailWord_3358762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358762).length < 2 ^ (prefixWord ++ tailWord_3358762).sum := by decide
  have hdescent : baseEnd_3358762 < baseStart_3358762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358768 : List Nat := [2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 4]
def baseStart_3358768 : Nat := 118140960795 + 3358768 * 2 ^ 59
def prefixEnd_3358768 : Nat := 4983230072969 + 3 ^ 40 * 3358768 * 2
def baseEnd_3358768 : Nat := 1724662390940620038453313

theorem tailTrace_3358768 : CollatzResearch.WordTrace tailWord_3358768 prefixEnd_3358768 1724662390940620038453313 := by
  unfold tailWord_3358768
  simp only [CollatzResearch.WordTrace]
  refine ⟨61252166547882321375170479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81669555397176428500227305 61252166547882321375170479)
  ·
    refine ⟨91878249821823482062755719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61252166547882321375170479 91878249821823482062755719)
    ·
      refine ⟨137817374732735223094133579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91878249821823482062755719 137817374732735223094133579)
      ·
        refine ⟨206726062099102834641200369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137817374732735223094133579 206726062099102834641200369)
        ·
          refine ⟨155044546574327125980900277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206726062099102834641200369 155044546574327125980900277)
          ·
            refine ⟨14535426241343168060709401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 155044546574327125980900277 14535426241343168060709401)
            ·
              refine ⟨10901569681007376045532051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14535426241343168060709401 10901569681007376045532051)
              ·
                refine ⟨16352354521511064068298077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10901569681007376045532051 16352354521511064068298077)
                ·
                  refine ⟨6132132945566649025611779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16352354521511064068298077 6132132945566649025611779)
                  ·
                    refine ⟨9198199418349973538417669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6132132945566649025611779 9198199418349973538417669)
                    ·
                      refine ⟨1724662390940620038453313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9198199418349973538417669 1724662390940620038453313)
                      ·
                        rfl

theorem cell23_3358768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 4].length) (baseStart_3358768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358768 prefixEnd_3358768 := by exact prefixLift 3358768
  have htrace : WordTrace (prefixWord ++ tailWord_3358768) baseStart_3358768 baseEnd_3358768 := by
    simpa [prefixWord, tailWord_3358768, baseEnd_3358768] using wordTrace_append hprefix tailTrace_3358768
  have hstable : (prefixWord ++ tailWord_3358768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358768).length < 2 ^ (prefixWord ++ tailWord_3358768).sum := by decide
  have hdescent : baseEnd_3358768 < baseStart_3358768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358778 : List Nat := [3, 1, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_3358778 : Nat := 118140960795 + 3358778 * 2 ^ 59
def prefixEnd_3358778 : Nat := 4983230072969 + 3 ^ 40 * 3358778 * 2
def baseEnd_3358778 : Nat := 574889175249054999776089

theorem tailTrace_3358778 : CollatzResearch.WordTrace tailWord_3358778 prefixEnd_3358778 574889175249054999776089 := by
  unfold tailWord_3358778
  simp only [CollatzResearch.WordTrace]
  refine ⟨30626174456432103614551247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81669798550485609638803325 30626174456432103614551247)
  ·
    refine ⟨45939261684648155421826871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30626174456432103614551247 45939261684648155421826871)
    ·
      refine ⟨68908892526972233132740307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45939261684648155421826871 68908892526972233132740307)
      ·
        refine ⟨103363338790458349699110461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68908892526972233132740307 103363338790458349699110461)
        ·
          refine ⟨38761252046421881137166423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103363338790458349699110461 38761252046421881137166423)
          ·
            refine ⟨58141878069632821705749635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38761252046421881137166423 58141878069632821705749635)
            ·
              refine ⟨87212817104449232558624453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58141878069632821705749635 87212817104449232558624453)
              ·
                refine ⟨16352403207084231104742085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87212817104449232558624453 16352403207084231104742085)
                ·
                  refine ⟨3066075601328293332139141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16352403207084231104742085 3066075601328293332139141)
                  ·
                    refine ⟨574889175249054999776089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066075601328293332139141 574889175249054999776089)
                    ·
                      rfl

theorem cell23_3358778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_3358778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358778 prefixEnd_3358778 := by exact prefixLift 3358778
  have htrace : WordTrace (prefixWord ++ tailWord_3358778) baseStart_3358778 baseEnd_3358778 := by
    simpa [prefixWord, tailWord_3358778, baseEnd_3358778] using wordTrace_append hprefix tailTrace_3358778
  have hstable : (prefixWord ++ tailWord_3358778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358778).length < 2 ^ (prefixWord ++ tailWord_3358778).sum := by decide
  have hdescent : baseEnd_3358778 < baseStart_3358778 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358782 : List Nat := [4, 2, 1, 3, 2, 1, 1, 3, 1, 5]
def baseStart_3358782 : Nat := 118140960795 + 3358782 * 2 ^ 59
def prefixEnd_3358782 : Nat := 4983230072969 + 3 ^ 40 * 3358782 * 2
def baseEnd_3358782 : Nat := 574889859889927661226083

theorem tailTrace_3358782 : CollatzResearch.WordTrace tailWord_3358782 prefixEnd_3358782 574889859889927661226083 := by
  unfold tailWord_3358782
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313105464714240392668825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81669895811809282094233733 15313105464714240392668825)
  ·
    refine ⟨11484829098535680294501619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15313105464714240392668825 11484829098535680294501619)
    ·
      refine ⟨17227243647803520441752429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11484829098535680294501619 17227243647803520441752429)
      ·
        refine ⟨6460216367926320165657161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17227243647803520441752429 6460216367926320165657161)
        ·
          refine ⟨4845162275944740124242871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6460216367926320165657161 4845162275944740124242871)
          ·
            refine ⟨7267743413917110186364307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4845162275944740124242871 7267743413917110186364307)
            ·
              refine ⟨10901615120875665279546461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7267743413917110186364307 10901615120875665279546461)
              ·
                refine ⟨4088105670328374479829923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10901615120875665279546461 4088105670328374479829923)
                ·
                  refine ⟨6132158505492561719744885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088105670328374479829923 6132158505492561719744885)
                  ·
                    refine ⟨574889859889927661226083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6132158505492561719744885 574889859889927661226083)
                    ·
                      rfl

theorem cell23_3358782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 1, 3, 1, 5].length) (baseStart_3358782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358782 prefixEnd_3358782 := by exact prefixLift 3358782
  have htrace : WordTrace (prefixWord ++ tailWord_3358782) baseStart_3358782 baseEnd_3358782 := by
    simpa [prefixWord, tailWord_3358782, baseEnd_3358782] using wordTrace_append hprefix tailTrace_3358782
  have hstable : (prefixWord ++ tailWord_3358782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358782).length < 2 ^ (prefixWord ++ tailWord_3358782).sum := by decide
  have hdescent : baseEnd_3358782 < baseStart_3358782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358791 : List Nat := [1, 1, 4, 1, 3, 1, 12]
def baseStart_3358791 : Nat := 118140960795 + 3358791 * 2 ^ 59
def prefixEnd_3358791 : Nat := 4983230072969 + 3 ^ 40 * 3358791 * 2
def baseEnd_3358791 : Nat := 21292274086366338869947

theorem tailTrace_3358791 : CollatzResearch.WordTrace tailWord_3358791 prefixEnd_3358791 21292274086366338869947 := by
  unfold tailWord_3358791
  simp only [CollatzResearch.WordTrace]
  refine ⟨122505171974681317678428227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81670114649787545118952151 122505171974681317678428227)
  ·
    refine ⟨183757757962021976517642341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122505171974681317678428227 183757757962021976517642341)
    ·
      refine ⟨34454579617879120597057939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183757757962021976517642341 34454579617879120597057939)
      ·
        refine ⟨51681869426818680895586909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34454579617879120597057939 51681869426818680895586909)
        ·
          refine ⟨19380701035057005335845091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51681869426818680895586909 19380701035057005335845091)
          ·
            refine ⟨29071051552585508003767637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19380701035057005335845091 29071051552585508003767637)
            ·
              refine ⟨21292274086366338869947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 29071051552585508003767637 21292274086366338869947)
              ·
                rfl

theorem cell23_3358791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 12].length) (baseStart_3358791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358791 prefixEnd_3358791 := by exact prefixLift 3358791
  have htrace : WordTrace (prefixWord ++ tailWord_3358791) baseStart_3358791 baseEnd_3358791 := by
    simpa [prefixWord, tailWord_3358791, baseEnd_3358791] using wordTrace_append hprefix tailTrace_3358791
  have hstable : (prefixWord ++ tailWord_3358791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358791).length < 2 ^ (prefixWord ++ tailWord_3358791).sum := by decide
  have hdescent : baseEnd_3358791 < baseStart_3358791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358801 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3358801 : Nat := 118140960795 + 3358801 * 2 ^ 59
def prefixEnd_3358801 : Nat := 4983230072969 + 3 ^ 40 * 3358801 * 2
def baseEnd_3358801 : Nat := 1724679335802218409340661

theorem tailTrace_3358801 : CollatzResearch.WordTrace tailWord_3358801 prefixEnd_3358801 1724679335802218409340661 := by
  unfold tailWord_3358801
  simp only [CollatzResearch.WordTrace]
  refine ⟨122505536704645089386292257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81670357803096726257528171 122505536704645089386292257)
  ·
    refine ⟨91879152528483817039719193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122505536704645089386292257 91879152528483817039719193)
    ·
      refine ⟨68909364396362862779789395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91879152528483817039719193 68909364396362862779789395)
      ·
        refine ⟨103364046594544294169684093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68909364396362862779789395 103364046594544294169684093)
        ·
          refine ⟨38761517472954110313631535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103364046594544294169684093 38761517472954110313631535)
          ·
            refine ⟨58142276209431165470447303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38761517472954110313631535 58142276209431165470447303)
            ·
              refine ⟨87213414314146748205670955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58142276209431165470447303 87213414314146748205670955)
              ·
                refine ⟨130820121471220122308506433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87213414314146748205670955 130820121471220122308506433)
                ·
                  refine ⟨98115091103415091731379825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 130820121471220122308506433 98115091103415091731379825)
                  ·
                    refine ⟨73586318327561318798534869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 98115091103415091731379825 73586318327561318798534869)
                    ·
                      refine ⟨1724679335802218409340661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73586318327561318798534869 1724679335802218409340661)
                      ·
                        rfl

theorem cell23_3358801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3358801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358801 prefixEnd_3358801 := by exact prefixLift 3358801
  have htrace : WordTrace (prefixWord ++ tailWord_3358801) baseStart_3358801 baseEnd_3358801 := by
    simpa [prefixWord, tailWord_3358801, baseEnd_3358801] using wordTrace_append hprefix tailTrace_3358801
  have hstable : (prefixWord ++ tailWord_3358801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358801).length < 2 ^ (prefixWord ++ tailWord_3358801).sum := by decide
  have hdescent : baseEnd_3358801 < baseStart_3358801 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358852 : List Nat := [2, 3, 2, 1, 2, 1, 2, 4, 2, 1, 3]
def baseStart_3358852 : Nat := 118140960795 + 3358852 * 2 ^ 59
def prefixEnd_3358852 : Nat := 4983230072969 + 3 ^ 40 * 3358852 * 2
def baseEnd_3358852 : Nat := 1724705523315597709802927

theorem tailTrace_3358852 : CollatzResearch.WordTrace tailWord_3358852 prefixEnd_3358852 1724705523315597709802927 := by
  unfold tailWord_3358852
  simp only [CollatzResearch.WordTrace]
  refine ⟨61253698413730162548199405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81671597884973550064265873 61253698413730162548199405)
  ·
    refine ⟨22970136905148810955574777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61253698413730162548199405 22970136905148810955574777)
    ·
      refine ⟨17227602678861608216681083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22970136905148810955574777 17227602678861608216681083)
      ·
        refine ⟨25841404018292412325021625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17227602678861608216681083 25841404018292412325021625)
        ·
          refine ⟨19381053013719309243766219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25841404018292412325021625 19381053013719309243766219)
          ·
            refine ⟨29071579520578963865649329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19381053013719309243766219 29071579520578963865649329)
            ·
              refine ⟨21803684640434222899236997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29071579520578963865649329 21803684640434222899236997)
              ·
                refine ⟨4088190870081416793606937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21803684640434222899236997 4088190870081416793606937)
                ·
                  refine ⟨3066143152561062595205203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4088190870081416793606937 3066143152561062595205203)
                  ·
                    refine ⟨4599214728841593892807805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3066143152561062595205203 4599214728841593892807805)
                    ·
                      refine ⟨1724705523315597709802927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599214728841593892807805 1724705523315597709802927)
                      ·
                        rfl

theorem cell23_3358852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_3358852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358852 prefixEnd_3358852 := by exact prefixLift 3358852
  have htrace : WordTrace (prefixWord ++ tailWord_3358852) baseStart_3358852 baseEnd_3358852 := by
    simpa [prefixWord, tailWord_3358852, baseEnd_3358852] using wordTrace_append hprefix tailTrace_3358852
  have hstable : (prefixWord ++ tailWord_3358852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358852).length < 2 ^ (prefixWord ++ tailWord_3358852).sum := by decide
  have hdescent : baseEnd_3358852 < baseStart_3358852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358870 : List Nat := [5, 3, 2, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_3358870 : Nat := 118140960795 + 3358870 * 2 ^ 59
def prefixEnd_3358870 : Nat := 4983230072969 + 3 ^ 40 * 3358870 * 2
def baseEnd_3358870 : Nat := 1724714765967378639377845

theorem tailTrace_3358870 : CollatzResearch.WordTrace tailWord_3358870 prefixEnd_3358870 1724714765967378639377845 := by
  unfold tailWord_3358870
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656753333837194635659629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81672035560930076113702709 7656753333837194635659629)
  ·
    refine ⟨2871282500188947988372361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7656753333837194635659629 2871282500188947988372361)
    ·
      refine ⟨2153461875141710991279271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2871282500188947988372361 2153461875141710991279271)
      ·
        refine ⟨3230192812712566486918907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2153461875141710991279271 3230192812712566486918907)
        ·
          refine ⟨4845289219068849730378361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3230192812712566486918907 4845289219068849730378361)
          ·
            refine ⟨3633966914301637297783771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4845289219068849730378361 3633966914301637297783771)
            ·
              refine ⟨5450950371452455946675657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633966914301637297783771 5450950371452455946675657)
              ·
                refine ⟨4088212778589341960006743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450950371452455946675657 4088212778589341960006743)
                ·
                  refine ⟨6132319167884012940010115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088212778589341960006743 6132319167884012940010115)
                  ·
                    refine ⟨9198478751826019410015173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6132319167884012940010115 9198478751826019410015173)
                    ·
                      refine ⟨1724714765967378639377845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9198478751826019410015173 1724714765967378639377845)
                      ·
                        rfl

theorem cell23_3358870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_3358870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358870 prefixEnd_3358870 := by exact prefixLift 3358870
  have htrace : WordTrace (prefixWord ++ tailWord_3358870) baseStart_3358870 baseEnd_3358870 := by
    simpa [prefixWord, tailWord_3358870, baseEnd_3358870] using wordTrace_append hprefix tailTrace_3358870
  have hstable : (prefixWord ++ tailWord_3358870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358870).length < 2 ^ (prefixWord ++ tailWord_3358870).sum := by decide
  have hdescent : baseEnd_3358870 < baseStart_3358870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358879 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 1, 3, 2]
def baseStart_3358879 : Nat := 118140960795 + 3358879 * 2 ^ 59
def prefixEnd_3358879 : Nat := 4983230072969 + 3 ^ 40 * 3358879 * 2
def baseEnd_3358879 : Nat := 1724719387293269104165303

theorem tailTrace_3358879 : CollatzResearch.WordTrace tailWord_3358879 prefixEnd_3358879 1724719387293269104165303 := by
  unfold tailWord_3358879
  simp only [CollatzResearch.WordTrace]
  refine ⟨122508381598362508707631691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81672254398908339138421127 122508381598362508707631691)
  ·
    refine ⟨183762572397543763061447537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122508381598362508707631691 183762572397543763061447537)
    ·
      refine ⟨137821929298157822296085653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183762572397543763061447537 137821929298157822296085653)
      ·
        refine ⟨6460402935851147920129015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137821929298157822296085653 6460402935851147920129015)
        ·
          refine ⟨9690604403776721880193523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460402935851147920129015 9690604403776721880193523)
          ·
            refine ⟨14535906605665082820290285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9690604403776721880193523 14535906605665082820290285)
            ·
              refine ⟨5450964977124406057608857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14535906605665082820290285 5450964977124406057608857)
              ·
                refine ⟨4088223732843304543206643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450964977124406057608857 4088223732843304543206643)
                ·
                  refine ⟨6132335599264956814809965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088223732843304543206643 6132335599264956814809965)
                  ·
                    refine ⟨2299625849724358805553737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6132335599264956814809965 2299625849724358805553737)
                    ·
                      refine ⟨1724719387293269104165303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299625849724358805553737 1724719387293269104165303)
                      ·
                        rfl

theorem cell23_3358879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_3358879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358879 prefixEnd_3358879 := by exact prefixLift 3358879
  have htrace : WordTrace (prefixWord ++ tailWord_3358879) baseStart_3358879 baseEnd_3358879 := by
    simpa [prefixWord, tailWord_3358879, baseEnd_3358879] using wordTrace_append hprefix tailTrace_3358879
  have hstable : (prefixWord ++ tailWord_3358879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358879).length < 2 ^ (prefixWord ++ tailWord_3358879).sum := by decide
  have hdescent : baseEnd_3358879 < baseStart_3358879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358935 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 4, 5, 2]
def baseStart_3358935 : Nat := 118140960795 + 3358935 * 2 ^ 59
def prefixEnd_3358935 : Nat := 4983230072969 + 3 ^ 40 * 3358935 * 2
def baseEnd_3358935 : Nat := 1724748142209920885065045

theorem tailTrace_3358935 : CollatzResearch.WordTrace tailWord_3358935 prefixEnd_3358935 1724748142209920885065045 := by
  unfold tailWord_3358935
  simp only [CollatzResearch.WordTrace]
  refine ⟨122510424086159630271670259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81673616057439753514446839 122510424086159630271670259)
  ·
    refine ⟨183765636129239445407505389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122510424086159630271670259 183765636129239445407505389)
    ·
      refine ⟨68912113548464792027814521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183765636129239445407505389 68912113548464792027814521)
      ·
        refine ⟨51684085161348594020860891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68912113548464792027814521 51684085161348594020860891)
        ·
          refine ⟨77526127742022891031291337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51684085161348594020860891 77526127742022891031291337)
          ·
            refine ⟨58144595806517168273468503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77526127742022891031291337 58144595806517168273468503)
            ·
              refine ⟨87216893709775752410202755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58144595806517168273468503 87216893709775752410202755)
              ·
                refine ⟨130825340564663628615304133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87216893709775752410202755 130825340564663628615304133)
                ·
                  refine ⟨24529751355874430365369525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130825340564663628615304133 24529751355874430365369525)
                  ·
                    refine ⟨2299664189613227846753393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24529751355874430365369525 2299664189613227846753393)
                    ·
                      refine ⟨1724748142209920885065045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299664189613227846753393 1724748142209920885065045)
                      ·
                        rfl

theorem cell23_3358935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4, 5, 2].length) (baseStart_3358935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358935 prefixEnd_3358935 := by exact prefixLift 3358935
  have htrace : WordTrace (prefixWord ++ tailWord_3358935) baseStart_3358935 baseEnd_3358935 := by
    simpa [prefixWord, tailWord_3358935, baseEnd_3358935] using wordTrace_append hprefix tailTrace_3358935
  have hstable : (prefixWord ++ tailWord_3358935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358935).length < 2 ^ (prefixWord ++ tailWord_3358935).sum := by decide
  have hdescent : baseEnd_3358935 < baseStart_3358935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358938 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_3358938 : Nat := 118140960795 + 3358938 * 2 ^ 59
def prefixEnd_3358938 : Nat := 4983230072969 + 3 ^ 40 * 3358938 * 2
def baseEnd_3358938 : Nat := 1724749682651884373327531

theorem tailTrace_3358938 : CollatzResearch.WordTrace tailWord_3358938 prefixEnd_3358938 1724749682651884373327531 := by
  unfold tailWord_3358938
  simp only [CollatzResearch.WordTrace]
  refine ⟨30627633376287190446007367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81673689003432507856019645 30627633376287190446007367)
  ·
    refine ⟨45941450064430785669011051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30627633376287190446007367 45941450064430785669011051)
    ·
      refine ⟨68912175096646178503516577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45941450064430785669011051 68912175096646178503516577)
      ·
        refine ⟨51684131322484633877637433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68912175096646178503516577 51684131322484633877637433)
        ·
          refine ⟨38763098491863475408228075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51684131322484633877637433 38763098491863475408228075)
          ·
            refine ⟨58144647737795213112342113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38763098491863475408228075 58144647737795213112342113)
            ·
              refine ⟨43608485803346409834256585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58144647737795213112342113 43608485803346409834256585)
              ·
                refine ⟨32706364352509807375692439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43608485803346409834256585 32706364352509807375692439)
                ·
                  refine ⟨49059546528764711063538659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32706364352509807375692439 49059546528764711063538659)
                  ·
                    refine ⟨73589319793147066595307989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49059546528764711063538659 73589319793147066595307989)
                    ·
                      refine ⟨1724749682651884373327531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73589319793147066595307989 1724749682651884373327531)
                      ·
                        rfl

theorem cell23_3358938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_3358938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358938 prefixEnd_3358938 := by exact prefixLift 3358938
  have htrace : WordTrace (prefixWord ++ tailWord_3358938) baseStart_3358938 baseEnd_3358938 := by
    simpa [prefixWord, tailWord_3358938, baseEnd_3358938] using wordTrace_append hprefix tailTrace_3358938
  have hstable : (prefixWord ++ tailWord_3358938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358938).length < 2 ^ (prefixWord ++ tailWord_3358938).sum := by decide
  have hdescent : baseEnd_3358938 < baseStart_3358938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358968 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_3358968 : Nat := 118140960795 + 3358968 * 2 ^ 59
def prefixEnd_3358968 : Nat := 4983230072969 + 3 ^ 40 * 3358968 * 2
def baseEnd_3358968 : Nat := 1724765087071519255952393

theorem tailTrace_3358968 : CollatzResearch.WordTrace tailWord_3358968 prefixEnd_3358968 1724765087071519255952393 := by
  unfold tailWord_3358968
  simp only [CollatzResearch.WordTrace]
  refine ⟨61255813847520038453810779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81674418463360051271747705 61255813847520038453810779)
  ·
    refine ⟨91883720771280057680716169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61255813847520038453810779 91883720771280057680716169)
    ·
      refine ⟨68912790578460043260537127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91883720771280057680716169 68912790578460043260537127)
      ·
        refine ⟨103369185867690064890805691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68912790578460043260537127 103369185867690064890805691)
        ·
          refine ⟨155053778801535097336208537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103369185867690064890805691 155053778801535097336208537)
          ·
            refine ⟨116290334101151323002156403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155053778801535097336208537 116290334101151323002156403)
            ·
              refine ⟨174435501151726984503234605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116290334101151323002156403 174435501151726984503234605)
              ·
                refine ⟨65413312931897619188712977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174435501151726984503234605 65413312931897619188712977)
                ·
                  refine ⟨49059984698923214391534733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65413312931897619188712977 49059984698923214391534733)
                  ·
                    refine ⟨18397494262096205396825525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49059984698923214391534733 18397494262096205396825525)
                    ·
                      refine ⟨1724765087071519255952393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18397494262096205396825525 1724765087071519255952393)
                      ·
                        rfl

theorem cell23_3358968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_3358968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358968 prefixEnd_3358968 := by exact prefixLift 3358968
  have htrace : WordTrace (prefixWord ++ tailWord_3358968) baseStart_3358968 baseEnd_3358968 := by
    simpa [prefixWord, tailWord_3358968, baseEnd_3358968] using wordTrace_append hprefix tailTrace_3358968
  have hstable : (prefixWord ++ tailWord_3358968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358968).length < 2 ^ (prefixWord ++ tailWord_3358968).sum := by decide
  have hdescent : baseEnd_3358968 < baseStart_3358968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3358985 : List Nat := [1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 3]
def baseStart_3358985 : Nat := 118140960795 + 3358985 * 2 ^ 59
def prefixEnd_3358985 : Nat := 4983230072969 + 3 ^ 40 * 3358985 * 2
def baseEnd_3358985 : Nat := 1724773816242645689439815

theorem tailTrace_3358985 : CollatzResearch.WordTrace tailWord_3358985 prefixEnd_3358985 1724773816242645689439815 := by
  unfold tailWord_3358985
  simp only [CollatzResearch.WordTrace]
  refine ⟨122512247735978488810990409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81674831823985659207326939 122512247735978488810990409)
  ·
    refine ⟨91884185801983866608242807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122512247735978488810990409 91884185801983866608242807)
    ·
      refine ⟨137826278702975799912364211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91884185801983866608242807 137826278702975799912364211)
      ·
        refine ⟨206739418054463699868546317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137826278702975799912364211 206739418054463699868546317)
        ·
          refine ⟨77527281770423887450704869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206739418054463699868546317 77527281770423887450704869)
          ·
            refine ⟨14536365331954478897007163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77527281770423887450704869 14536365331954478897007163)
            ·
              refine ⟨21804547997931718345510745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14536365331954478897007163 21804547997931718345510745)
              ·
                refine ⟨16353410998448788759133059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21804547997931718345510745 16353410998448788759133059)
                ·
                  refine ⟨24530116497673183138699589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16353410998448788759133059 24530116497673183138699589)
                  ·
                    refine ⟨4599396843313721838506173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24530116497673183138699589 4599396843313721838506173)
                    ·
                      refine ⟨1724773816242645689439815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599396843313721838506173 1724773816242645689439815)
                      ·
                        rfl

theorem cell23_3358985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 3].length) (baseStart_3358985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3358985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3358985 prefixEnd_3358985 := by exact prefixLift 3358985
  have htrace : WordTrace (prefixWord ++ tailWord_3358985) baseStart_3358985 baseEnd_3358985 := by
    simpa [prefixWord, tailWord_3358985, baseEnd_3358985] using wordTrace_append hprefix tailTrace_3358985
  have hstable : (prefixWord ++ tailWord_3358985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3358985).length < 2 ^ (prefixWord ++ tailWord_3358985).sum := by decide
  have hdescent : baseEnd_3358985 < baseStart_3358985 := by decide
  rcases family_descends (prefixWord ++ tailWord_3358985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359009 : List Nat := [1, 2, 3, 2, 1, 1, 5, 3, 1, 4]
def baseStart_3359009 : Nat := 118140960795 + 3359009 * 2 ^ 59
def prefixEnd_3359009 : Nat := 4983230072969 + 3 ^ 40 * 3359009 * 2
def baseEnd_3359009 : Nat := 574928713259451198513235

theorem tailTrace_3359009 : CollatzResearch.WordTrace tailWord_3359009 prefixEnd_3359009 574928713259451198513235 := by
  unfold tailWord_3359009
  simp only [CollatzResearch.WordTrace]
  refine ⟨122513123087891540909864081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81675415391927693939909387 122513123087891540909864081)
  ·
    refine ⟨91884842315918655682398061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122513123087891540909864081 91884842315918655682398061)
    ·
      refine ⟨34456815868469495880899273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91884842315918655682398061 34456815868469495880899273)
      ·
        refine ⟨25842611901352121910674455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34456815868469495880899273 25842611901352121910674455)
        ·
          refine ⟨38763917852028182866011683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25842611901352121910674455 38763917852028182866011683)
          ·
            refine ⟨58145876778042274299017525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38763917852028182866011683 58145876778042274299017525)
            ·
              refine ⟨5451175947941463215532893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58145876778042274299017525 5451175947941463215532893)
              ·
                refine ⟨2044190980478048705824835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5451175947941463215532893 2044190980478048705824835)
                ·
                  refine ⟨3066286470717073058737253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044190980478048705824835 3066286470717073058737253)
                  ·
                    refine ⟨574928713259451198513235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066286470717073058737253 574928713259451198513235)
                    ·
                      rfl

theorem cell23_3359009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_3359009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359009 prefixEnd_3359009 := by exact prefixLift 3359009
  have htrace : WordTrace (prefixWord ++ tailWord_3359009) baseStart_3359009 baseEnd_3359009 := by
    simpa [prefixWord, tailWord_3359009, baseEnd_3359009] using wordTrace_append hprefix tailTrace_3359009
  have hstable : (prefixWord ++ tailWord_3359009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359009).length < 2 ^ (prefixWord ++ tailWord_3359009).sum := by decide
  have hdescent : baseEnd_3359009 < baseStart_3359009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359026 : List Nat := [3, 2, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_3359026 : Nat := 118140960795 + 3359026 * 2 ^ 59
def prefixEnd_3359026 : Nat := 4983230072969 + 3 ^ 40 * 3359026 * 2
def baseEnd_3359026 : Nat := 574931622983160009675709

theorem tailTrace_3359026 : CollatzResearch.WordTrace tailWord_3359026 prefixEnd_3359026 574931622983160009675709 := by
  unfold tailWord_3359026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30628435782207488203308233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81675828752553301875488621 30628435782207488203308233)
  ·
    refine ⟨22971326836655616152481175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30628435782207488203308233 22971326836655616152481175)
    ·
      refine ⟨34456990254983424228721763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22971326836655616152481175 34456990254983424228721763)
      ·
        refine ⟨51685485382475136343082645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34456990254983424228721763 51685485382475136343082645)
        ·
          refine ⟨2422757127303522016081999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51685485382475136343082645 2422757127303522016081999)
          ·
            refine ⟨3634135690955283024122999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422757127303522016081999 3634135690955283024122999)
            ·
              refine ⟨5451203536432924536184499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634135690955283024122999 5451203536432924536184499)
              ·
                refine ⟨8176805304649386804276749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451203536432924536184499 8176805304649386804276749)
                ·
                  refine ⟨3066301989243520051603781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8176805304649386804276749 3066301989243520051603781)
                  ·
                    refine ⟨574931622983160009675709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066301989243520051603781 574931622983160009675709)
                    ·
                      rfl

theorem cell23_3359026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_3359026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359026 prefixEnd_3359026 := by exact prefixLift 3359026
  have htrace : WordTrace (prefixWord ++ tailWord_3359026) baseStart_3359026 baseEnd_3359026 := by
    simpa [prefixWord, tailWord_3359026, baseEnd_3359026] using wordTrace_append hprefix tailTrace_3359026
  have hstable : (prefixWord ++ tailWord_3359026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359026).length < 2 ^ (prefixWord ++ tailWord_3359026).sum := by decide
  have hdescent : baseEnd_3359026 < baseStart_3359026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359089 : List Nat := [1, 2, 2, 2, 1, 2, 1, 5, 3, 2, 2]
def baseStart_3359089 : Nat := 118140960795 + 3359089 * 2 ^ 59
def prefixEnd_3359089 : Nat := 4983230072969 + 3 ^ 40 * 3359089 * 2
def baseEnd_3359089 : Nat := 1724827218230713282539337

theorem tailTrace_3359089 : CollatzResearch.WordTrace tailWord_3359089 prefixEnd_3359089 1724827218230713282539337 := by
  unfold tailWord_3359089
  simp only [CollatzResearch.WordTrace]
  refine ⟨122516040927601714572776321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81677360618401143048517547 122516040927601714572776321)
  ·
    refine ⟨91887030695701285929582241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122516040927601714572776321 91887030695701285929582241)
    ·
      refine ⟨68915273021775964447186681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91887030695701285929582241 68915273021775964447186681)
      ·
        refine ⟨51686454766331973335390011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68915273021775964447186681 51686454766331973335390011)
        ·
          refine ⟨77529682149497960003085017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51686454766331973335390011 77529682149497960003085017)
          ·
            refine ⟨58147261612123470002313763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77529682149497960003085017 58147261612123470002313763)
            ·
              refine ⟨87220892418185205003470645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58147261612123470002313763 87220892418185205003470645)
              ·
                refine ⟨8176958664204862969075373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87220892418185205003470645 8176958664204862969075373)
                ·
                  refine ⟨3066359499076823613403265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8176958664204862969075373 3066359499076823613403265)
                  ·
                    refine ⟨2299769624307617710052449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3066359499076823613403265 2299769624307617710052449)
                    ·
                      refine ⟨1724827218230713282539337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299769624307617710052449 1724827218230713282539337)
                      ·
                        rfl

theorem cell23_3359089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 5, 3, 2, 2].length) (baseStart_3359089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359089 prefixEnd_3359089 := by exact prefixLift 3359089
  have htrace : WordTrace (prefixWord ++ tailWord_3359089) baseStart_3359089 baseEnd_3359089 := by
    simpa [prefixWord, tailWord_3359089, baseEnd_3359089] using wordTrace_append hprefix tailTrace_3359089
  have hstable : (prefixWord ++ tailWord_3359089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359089).length < 2 ^ (prefixWord ++ tailWord_3359089).sum := by decide
  have hdescent : baseEnd_3359089 < baseStart_3359089 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359112 : List Nat := [2, 1, 3, 3, 1, 1, 5, 7]
def baseStart_3359112 : Nat := 118140960795 + 3359112 * 2 ^ 59
def prefixEnd_3359112 : Nat := 4983230072969 + 3 ^ 40 * 3359112 * 2
def baseEnd_3359112 : Nat := 63882926973546914538953

theorem tailTrace_3359112 : CollatzResearch.WordTrace tailWord_3359112 prefixEnd_3359112 63882926973546914538953 := by
  unfold tailWord_3359112
  simp only [CollatzResearch.WordTrace]
  refine ⟨61258439903259194750431795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81677919871012259667242393 61258439903259194750431795)
  ·
    refine ⟨91887659854888792125647693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61258439903259194750431795 91887659854888792125647693)
    ·
      refine ⟨34457872445583297047117885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91887659854888792125647693 34457872445583297047117885)
      ·
        refine ⟨12921702167093736392669207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34457872445583297047117885 12921702167093736392669207)
        ·
          refine ⟨19382553250640604589003811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12921702167093736392669207 19382553250640604589003811)
          ·
            refine ⟨29073829875960906883505717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19382553250640604589003811 29073829875960906883505717)
            ·
              refine ⟨2725671550871335020328661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29073829875960906883505717 2725671550871335020328661)
              ·
                refine ⟨63882926973546914538953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2725671550871335020328661 63882926973546914538953)
                ·
                  rfl

theorem cell23_3359112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 5, 7].length) (baseStart_3359112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359112 prefixEnd_3359112 := by exact prefixLift 3359112
  have htrace : WordTrace (prefixWord ++ tailWord_3359112) baseStart_3359112 baseEnd_3359112 := by
    simpa [prefixWord, tailWord_3359112, baseEnd_3359112] using wordTrace_append hprefix tailTrace_3359112
  have hstable : (prefixWord ++ tailWord_3359112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359112).length < 2 ^ (prefixWord ++ tailWord_3359112).sum := by decide
  have hdescent : baseEnd_3359112 < baseStart_3359112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359133 : List Nat := [1, 4, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_3359133 : Nat := 118140960795 + 3359133 * 2 ^ 59
def prefixEnd_3359133 : Nat := 4983230072969 + 3 ^ 40 * 3359133 * 2
def baseEnd_3359133 : Nat := 574949937126503703463045

theorem tailTrace_3359133 : CollatzResearch.WordTrace tailWord_3359133 prefixEnd_3359133 574949937126503703463045 := by
  unfold tailWord_3359133
  simp only [CollatzResearch.WordTrace]
  refine ⟨122517645739442310087378053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81678430492961540058252035 122517645739442310087378053)
  ·
    refine ⟨22972058576145433141383385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122517645739442310087378053 22972058576145433141383385)
    ·
      refine ⟨17229043932109074856037539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22972058576145433141383385 17229043932109074856037539)
      ·
        refine ⟨25843565898163612284056309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17229043932109074856037539 25843565898163612284056309)
        ·
          refine ⟨2422834302952838651630279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25843565898163612284056309 2422834302952838651630279)
          ·
            refine ⟨3634251454429257977445419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422834302952838651630279 3634251454429257977445419)
            ·
              refine ⟨5451377181643886966168129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634251454429257977445419 5451377181643886966168129)
              ·
                refine ⟨4088532886232915224626097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5451377181643886966168129 4088532886232915224626097)
                ·
                  refine ⟨3066399664674686418469573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4088532886232915224626097 3066399664674686418469573)
                  ·
                    refine ⟨574949937126503703463045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066399664674686418469573 574949937126503703463045)
                    ·
                      rfl

theorem cell23_3359133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_3359133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359133 prefixEnd_3359133 := by exact prefixLift 3359133
  have htrace : WordTrace (prefixWord ++ tailWord_3359133) baseStart_3359133 baseEnd_3359133 := by
    simpa [prefixWord, tailWord_3359133, baseEnd_3359133] using wordTrace_append hprefix tailTrace_3359133
  have hstable : (prefixWord ++ tailWord_3359133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359133).length < 2 ^ (prefixWord ++ tailWord_3359133).sum := by decide
  have hdescent : baseEnd_3359133 < baseStart_3359133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359139 : List Nat := [1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 3]
def baseStart_3359139 : Nat := 118140960795 + 3359139 * 2 ^ 59
def prefixEnd_3359139 : Nat := 4983230072969 + 3 ^ 40 * 3359139 * 2
def baseEnd_3359139 : Nat := 1724852892263438086914107

theorem tailTrace_3359139 : CollatzResearch.WordTrace tailWord_3359139 prefixEnd_3359139 1724852892263438086914107 := by
  unfold tailWord_3359139
  simp only [CollatzResearch.WordTrace]
  refine ⟨122517864577420573112096471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81678576384947048741397647 122517864577420573112096471)
  ·
    refine ⟨183776796866130859668144707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122517864577420573112096471 183776796866130859668144707)
    ·
      refine ⟨275665195299196289502217061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183776796866130859668144707 275665195299196289502217061)
      ·
        refine ⟨51687224118599304281665699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275665195299196289502217061 51687224118599304281665699)
        ·
          refine ⟨77530836177898956422498549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51687224118599304281665699 77530836177898956422498549)
          ·
            refine ⟨7268515891678027164609239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77530836177898956422498549 7268515891678027164609239)
            ·
              refine ⟨10902773837517040746913859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7268515891678027164609239 10902773837517040746913859)
              ·
                refine ⟨16354160756275561120370789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10902773837517040746913859 16354160756275561120370789)
                ·
                  refine ⟨3066405141801667710069523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16354160756275561120370789 3066405141801667710069523)
                  ·
                    refine ⟨4599607712702501565104285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3066405141801667710069523 4599607712702501565104285)
                    ·
                      refine ⟨1724852892263438086914107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599607712702501565104285 1724852892263438086914107)
                      ·
                        rfl

theorem cell23_3359139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 3].length) (baseStart_3359139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359139 prefixEnd_3359139 := by exact prefixLift 3359139
  have htrace : WordTrace (prefixWord ++ tailWord_3359139) baseStart_3359139 baseEnd_3359139 := by
    simpa [prefixWord, tailWord_3359139, baseEnd_3359139] using wordTrace_append hprefix tailTrace_3359139
  have hstable : (prefixWord ++ tailWord_3359139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359139).length < 2 ^ (prefixWord ++ tailWord_3359139).sum := by decide
  have hdescent : baseEnd_3359139 < baseStart_3359139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359145 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_3359145 : Nat := 118140960795 + 3359145 * 2 ^ 59
def prefixEnd_3359145 : Nat := 4983230072969 + 3 ^ 40 * 3359145 * 2
def baseEnd_3359145 : Nat := 1724855973147365063439079

theorem tailTrace_3359145 : CollatzResearch.WordTrace tailWord_3359145 prefixEnd_3359145 1724855973147365063439079 := by
  unfold tailWord_3359145
  simp only [CollatzResearch.WordTrace]
  refine ⟨122518083415398836136814889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81678722276932557424543259 122518083415398836136814889)
  ·
    refine ⟨91888562561549127102611167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122518083415398836136814889 91888562561549127102611167)
    ·
      refine ⟨137832843842323690653916751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91888562561549127102611167 137832843842323690653916751)
      ·
        refine ⟨206749265763485535980875127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137832843842323690653916751 206749265763485535980875127)
        ·
          refine ⟨310123898645228303971312691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206749265763485535980875127 310123898645228303971312691)
          ·
            refine ⟨465185847967842455956969037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310123898645228303971312691 465185847967842455956969037)
            ·
              refine ⟨174444692987940920983863389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465185847967842455956969037 174444692987940920983863389)
              ·
                refine ⟨65416759870477845368948771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174444692987940920983863389 65416759870477845368948771)
                ·
                  refine ⟨98125139805716768053423157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65416759870477845368948771 98125139805716768053423157)
                  ·
                    refine ⟨9199231856785947005008421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 98125139805716768053423157 9199231856785947005008421)
                    ·
                      refine ⟨1724855973147365063439079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9199231856785947005008421 1724855973147365063439079)
                      ·
                        rfl

theorem cell23_3359145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_3359145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359145 prefixEnd_3359145 := by exact prefixLift 3359145
  have htrace : WordTrace (prefixWord ++ tailWord_3359145) baseStart_3359145 baseEnd_3359145 := by
    simpa [prefixWord, tailWord_3359145, baseEnd_3359145] using wordTrace_append hprefix tailTrace_3359145
  have hstable : (prefixWord ++ tailWord_3359145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359145).length < 2 ^ (prefixWord ++ tailWord_3359145).sum := by decide
  have hdescent : baseEnd_3359145 < baseStart_3359145 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359166 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2]
def baseStart_3359166 : Nat := 118140960795 + 3359166 * 2 ^ 59
def prefixEnd_3359166 : Nat := 4983230072969 + 3 ^ 40 * 3359166 * 2
def baseEnd_3359166 : Nat := 1724866756241109481276483

theorem tailTrace_3359166 : CollatzResearch.WordTrace tailWord_3359166 prefixEnd_3359166 1724866756241109481276483 := by
  unfold tailWord_3359166
  simp only [CollatzResearch.WordTrace]
  refine ⟨15314856168540344590416169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81679232898881837815552901 15314856168540344590416169)
  ·
    refine ⟨11486142126405258442812127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15314856168540344590416169 11486142126405258442812127)
    ·
      refine ⟨17229213189607887664218191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11486142126405258442812127 17229213189607887664218191)
      ·
        refine ⟨25843819784411831496327287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17229213189607887664218191 25843819784411831496327287)
        ·
          refine ⟨38765729676617747244490931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25843819784411831496327287 38765729676617747244490931)
          ·
            refine ⟨58148594514926620866736397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38765729676617747244490931 58148594514926620866736397)
            ·
              refine ⟨21805722943097482825026149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58148594514926620866736397 21805722943097482825026149)
              ·
                refine ⟨4088573051830778029692403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21805722943097482825026149 4088573051830778029692403)
                ·
                  refine ⟨6132859577746167044538605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088573051830778029692403 6132859577746167044538605)
                  ·
                    refine ⟨2299822341654812641701977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6132859577746167044538605 2299822341654812641701977)
                    ·
                      refine ⟨1724866756241109481276483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299822341654812641701977 1724866756241109481276483)
                      ·
                        rfl

theorem cell23_3359166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_3359166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359166 prefixEnd_3359166 := by exact prefixLift 3359166
  have htrace : WordTrace (prefixWord ++ tailWord_3359166) baseStart_3359166 baseEnd_3359166 := by
    simpa [prefixWord, tailWord_3359166, baseEnd_3359166] using wordTrace_append hprefix tailTrace_3359166
  have hstable : (prefixWord ++ tailWord_3359166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359166).length < 2 ^ (prefixWord ++ tailWord_3359166).sum := by decide
  have hdescent : baseEnd_3359166 < baseStart_3359166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359182 : List Nat := [4, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3]
def baseStart_3359182 : Nat := 118140960795 + 3359182 * 2 ^ 59
def prefixEnd_3359182 : Nat := 4983230072969 + 3 ^ 40 * 3359182 * 2
def baseEnd_3359182 : Nat := 1724874971931581418676409

theorem tailTrace_3359182 : CollatzResearch.WordTrace tailWord_3359182 prefixEnd_3359182 1724874971931581418676409 := by
  unfold tailWord_3359182
  simp only [CollatzResearch.WordTrace]
  refine ⟨15314929114533098931988975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81679621944176527637274533 15314929114533098931988975)
  ·
    refine ⟨22972393671799648397983463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15314929114533098931988975 22972393671799648397983463)
    ·
      refine ⟨34458590507699472596975195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22972393671799648397983463 34458590507699472596975195)
      ·
        refine ⟨51687885761549208895462793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34458590507699472596975195 51687885761549208895462793)
        ·
          refine ⟨38765914321161906671597095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51687885761549208895462793 38765914321161906671597095)
          ·
            refine ⟨58148871481742860007395643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38765914321161906671597095 58148871481742860007395643)
            ·
              refine ⟨87223307222614290011093465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58148871481742860007395643 87223307222614290011093465)
              ·
                refine ⟨65417480416960717508320099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87223307222614290011093465 65417480416960717508320099)
                ·
                  refine ⟨98126220625441076262480149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65417480416960717508320099 98126220625441076262480149)
                  ·
                    refine ⟨4599666591817550449803757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98126220625441076262480149 4599666591817550449803757)
                    ·
                      refine ⟨1724874971931581418676409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599666591817550449803757 1724874971931581418676409)
                      ·
                        rfl

theorem cell23_3359182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 1, 6, 3].length) (baseStart_3359182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359182 prefixEnd_3359182 := by exact prefixLift 3359182
  have htrace : WordTrace (prefixWord ++ tailWord_3359182) baseStart_3359182 baseEnd_3359182 := by
    simpa [prefixWord, tailWord_3359182, baseEnd_3359182] using wordTrace_append hprefix tailTrace_3359182
  have hstable : (prefixWord ++ tailWord_3359182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359182).length < 2 ^ (prefixWord ++ tailWord_3359182).sum := by decide
  have hdescent : baseEnd_3359182 < baseStart_3359182 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359185 : List Nat := [1, 2, 2, 1, 2, 1, 1, 4, 9]
def baseStart_3359185 : Nat := 118140960795 + 3359185 * 2 ^ 59
def prefixEnd_3359185 : Nat := 4983230072969 + 3 ^ 40 * 3359185 * 2
def baseEnd_3359185 : Nat := 191652945819282767437655

theorem tailTrace_3359185 : CollatzResearch.WordTrace tailWord_3359185 prefixEnd_3359185 191652945819282767437655 := by
  unfold tailWord_3359185
  simp only [CollatzResearch.WordTrace]
  refine ⟨122519542335253922968271009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81679694890169281978847339 122519542335253922968271009)
  ·
    refine ⟨91889656751440442226203257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122519542335253922968271009 91889656751440442226203257)
    ·
      refine ⟨68917242563580331669652443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91889656751440442226203257 68917242563580331669652443)
      ·
        refine ⟨103375863845370497504478665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68917242563580331669652443 103375863845370497504478665)
        ·
          refine ⟨77531897884027873128358999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103375863845370497504478665 77531897884027873128358999)
          ·
            refine ⟨116297846826041809692538499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77531897884027873128358999 116297846826041809692538499)
            ·
              refine ⟨174446770239062714538807749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116297846826041809692538499 174446770239062714538807749)
              ·
                refine ⟨32708769419824258976026453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174446770239062714538807749 32708769419824258976026453)
                ·
                  refine ⟨191652945819282767437655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32708769419824258976026453 191652945819282767437655)
                  ·
                    rfl

theorem cell23_3359185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 4, 9].length) (baseStart_3359185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359185 prefixEnd_3359185 := by exact prefixLift 3359185
  have htrace : WordTrace (prefixWord ++ tailWord_3359185) baseStart_3359185 baseEnd_3359185 := by
    simpa [prefixWord, tailWord_3359185, baseEnd_3359185] using wordTrace_append hprefix tailTrace_3359185
  have hstable : (prefixWord ++ tailWord_3359185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359185).length < 2 ^ (prefixWord ++ tailWord_3359185).sum := by decide
  have hdescent : baseEnd_3359185 < baseStart_3359185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359212 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_3359212 : Nat := 118140960795 + 3359212 * 2 ^ 59
def prefixEnd_3359212 : Nat := 4983230072969 + 3 ^ 40 * 3359212 * 2
def baseEnd_3359212 : Nat := 1724890376351216301301271

theorem tailTrace_3359212 : CollatzResearch.WordTrace tailWord_3359212 prefixEnd_3359212 1724890376351216301301271 := by
  unfold tailWord_3359212
  simp only [CollatzResearch.WordTrace]
  refine ⟨61260263553078053289751945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81680351404104071053002593 61260263553078053289751945)
  ·
    refine ⟨45945197664808539967313959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61260263553078053289751945 45945197664808539967313959)
    ·
      refine ⟨68917796497212809950970939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45945197664808539967313959 68917796497212809950970939)
      ·
        refine ⟨103376694745819214926456409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68917796497212809950970939 103376694745819214926456409)
        ·
          refine ⟨77532521059364411194842307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103376694745819214926456409 77532521059364411194842307)
          ·
            refine ⟨116298781589046616792263461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77532521059364411194842307 116298781589046616792263461)
            ·
              refine ⟨21806021547946240648549399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116298781589046616792263461 21806021547946240648549399)
              ·
                refine ⟨32709032321919360972824099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21806021547946240648549399 32709032321919360972824099)
                ·
                  refine ⟨49063548482879041459236149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32709032321919360972824099 49063548482879041459236149)
                  ·
                    refine ⟨4599707670269910136803389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49063548482879041459236149 4599707670269910136803389)
                    ·
                      refine ⟨1724890376351216301301271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599707670269910136803389 1724890376351216301301271)
                      ·
                        rfl

theorem cell23_3359212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_3359212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359212 prefixEnd_3359212 := by exact prefixLift 3359212
  have htrace : WordTrace (prefixWord ++ tailWord_3359212) baseStart_3359212 baseEnd_3359212 := by
    simpa [prefixWord, tailWord_3359212, baseEnd_3359212] using wordTrace_append hprefix tailTrace_3359212
  have hstable : (prefixWord ++ tailWord_3359212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359212).length < 2 ^ (prefixWord ++ tailWord_3359212).sum := by decide
  have hdescent : baseEnd_3359212 < baseStart_3359212 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359242 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_3359242 : Nat := 118140960795 + 3359242 * 2 ^ 59
def prefixEnd_3359242 : Nat := 4983230072969 + 3 ^ 40 * 3359242 * 2
def baseEnd_3359242 : Nat := 1724905780770851183926133

theorem tailTrace_3359242 : CollatzResearch.WordTrace tailWord_3359242 prefixEnd_3359242 1724905780770851183926133 := by
  unfold tailWord_3359242
  simp only [CollatzResearch.WordTrace]
  refine ⟨30630405324011855425773995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81681080864031614468730653 30630405324011855425773995)
  ·
    refine ⟨45945607986017783138660993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30630405324011855425773995 45945607986017783138660993)
    ·
      refine ⟨34459205989513337353995745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45945607986017783138660993 34459205989513337353995745)
      ·
        refine ⟨25844404492135003015496809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34459205989513337353995745 25844404492135003015496809)
        ·
          refine ⟨19383303369101252261622607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25844404492135003015496809 19383303369101252261622607)
          ·
            refine ⟨29074955053651878392433911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19383303369101252261622607 29074955053651878392433911)
            ·
              refine ⟨43612432580477817588650867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29074955053651878392433911 43612432580477817588650867)
              ·
                refine ⟨65418648870716726382976301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43612432580477817588650867 65418648870716726382976301)
                ·
                  refine ⟨24531993326518772393616113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65418648870716726382976301 24531993326518772393616113)
                  ·
                    refine ⟨18398994994889079295212085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24531993326518772393616113 18398994994889079295212085)
                    ·
                      refine ⟨1724905780770851183926133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18398994994889079295212085 1724905780770851183926133)
                      ·
                        rfl

theorem cell23_3359242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_3359242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359242 prefixEnd_3359242 := by exact prefixLift 3359242
  have htrace : WordTrace (prefixWord ++ tailWord_3359242) baseStart_3359242 baseEnd_3359242 := by
    simpa [prefixWord, tailWord_3359242, baseEnd_3359242] using wordTrace_append hprefix tailTrace_3359242
  have hstable : (prefixWord ++ tailWord_3359242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359242).length < 2 ^ (prefixWord ++ tailWord_3359242).sum := by decide
  have hdescent : baseEnd_3359242 < baseStart_3359242 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359269 : List Nat := [1, 3, 1, 2, 2, 1, 3, 1, 1, 6, 2]
def baseStart_3359269 : Nat := 118140960795 + 3359269 * 2 ^ 59
def prefixEnd_3359269 : Nat := 4983230072969 + 3 ^ 40 * 3359269 * 2
def baseEnd_3359269 : Nat := 1724919644748522578288509

theorem tailTrace_3359269 : CollatzResearch.WordTrace tailWord_3359269 prefixEnd_3359269 1724919644748522578288509 := by
  unfold tailWord_3359269
  simp only [CollatzResearch.WordTrace]
  refine ⟨122522606066949605314328861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81681737377966403542885907 122522606066949605314328861)
  ·
    refine ⟨45945977275106101992873323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122522606066949605314328861 45945977275106101992873323)
    ·
      refine ⟨68918965912659152989309985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45945977275106101992873323 68918965912659152989309985)
      ·
        refine ⟨51689224434494364741982489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68918965912659152989309985 51689224434494364741982489)
        ·
          refine ⟨38766918325870773556486867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51689224434494364741982489 38766918325870773556486867)
          ·
            refine ⟨58150377488806160334730301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38766918325870773556486867 58150377488806160334730301)
            ·
              refine ⟨21806391558302310125523863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58150377488806160334730301 21806391558302310125523863)
              ·
                refine ⟨32709587337453465188285795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21806391558302310125523863 32709587337453465188285795)
                ·
                  refine ⟨49064381006180197782428693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32709587337453465188285795 49064381006180197782428693)
                  ·
                    refine ⟨2299892859664696771051345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49064381006180197782428693 2299892859664696771051345)
                    ·
                      refine ⟨1724919644748522578288509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299892859664696771051345 1724919644748522578288509)
                      ·
                        rfl

theorem cell23_3359269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 1, 1, 6, 2].length) (baseStart_3359269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359269 prefixEnd_3359269 := by exact prefixLift 3359269
  have htrace : WordTrace (prefixWord ++ tailWord_3359269) baseStart_3359269 baseEnd_3359269 := by
    simpa [prefixWord, tailWord_3359269, baseEnd_3359269] using wordTrace_append hprefix tailTrace_3359269
  have hstable : (prefixWord ++ tailWord_3359269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359269).length < 2 ^ (prefixWord ++ tailWord_3359269).sum := by decide
  have hdescent : baseEnd_3359269 < baseStart_3359269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359286 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4]
def baseStart_3359286 : Nat := 118140960795 + 3359286 * 2 ^ 59
def prefixEnd_3359286 : Nat := 4983230072969 + 3 ^ 40 * 3359286 * 2
def baseEnd_3359286 : Nat := 1724928373919649011775931

theorem tailTrace_3359286 : CollatzResearch.WordTrace tailWord_3359286 prefixEnd_3359286 1724928373919649011775931 := by
  unfold tailWord_3359286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7657701631743001076106107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81682150738592011478465141 7657701631743001076106107)
  ·
    refine ⟨11486552447614501614159161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7657701631743001076106107 11486552447614501614159161)
    ·
      refine ⟨8614914335710876210619371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11486552447614501614159161 8614914335710876210619371)
      ·
        refine ⟨12922371503566314315929057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8614914335710876210619371 12922371503566314315929057)
        ·
          refine ⟨9691778627674735736946793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12922371503566314315929057 9691778627674735736946793)
          ·
            refine ⟨7268833970756051802710095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9691778627674735736946793 7268833970756051802710095)
            ·
              refine ⟨10903250956134077704065143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7268833970756051802710095 10903250956134077704065143)
              ·
                refine ⟨16354876434201116556097715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10903250956134077704065143 16354876434201116556097715)
                ·
                  refine ⟨24532314651301674834146573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16354876434201116556097715 24532314651301674834146573)
                  ·
                    refine ⟨9199617994238128062804965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24532314651301674834146573 9199617994238128062804965)
                    ·
                      refine ⟨1724928373919649011775931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9199617994238128062804965 1724928373919649011775931)
                      ·
                        rfl

theorem cell23_3359286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_3359286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359286 prefixEnd_3359286 := by exact prefixLift 3359286
  have htrace : WordTrace (prefixWord ++ tailWord_3359286) baseStart_3359286 baseEnd_3359286 := by
    simpa [prefixWord, tailWord_3359286, baseEnd_3359286] using wordTrace_append hprefix tailTrace_3359286
  have hstable : (prefixWord ++ tailWord_3359286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359286).length < 2 ^ (prefixWord ++ tailWord_3359286).sum := by decide
  have hdescent : baseEnd_3359286 < baseStart_3359286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359289 : List Nat := [1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3359289 : Nat := 118140960795 + 3359289 * 2 ^ 59
def prefixEnd_3359289 : Nat := 4983230072969 + 3 ^ 40 * 3359289 * 2
def baseEnd_3359289 : Nat := 1724929914361612500038417

theorem tailTrace_3359289 : CollatzResearch.WordTrace tailWord_3359289 prefixEnd_3359289 1724929914361612500038417 := by
  unfold tailWord_3359289
  simp only [CollatzResearch.WordTrace]
  refine ⟨122523335526877148730056921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81682223684584765820037947 122523335526877148730056921)
  ·
    refine ⟨91892501645157861547542691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122523335526877148730056921 91892501645157861547542691)
    ·
      refine ⟨137838752467736792321314037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91892501645157861547542691 137838752467736792321314037)
      ·
        refine ⟨12922383043850324280123191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137838752467736792321314037 12922383043850324280123191)
        ·
          refine ⟨19383574565775486420184787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12922383043850324280123191 19383574565775486420184787)
          ·
            refine ⟨29075361848663229630277181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19383574565775486420184787 29075361848663229630277181)
            ·
              refine ⟨10903260693248711111353943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29075361848663229630277181 10903260693248711111353943)
              ·
                refine ⟨16354891039873066667030915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10903260693248711111353943 16354891039873066667030915)
                ·
                  refine ⟨24532336559809600000546373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16354891039873066667030915 24532336559809600000546373)
                  ·
                    refine ⟨4599813104964300000102445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24532336559809600000546373 4599813104964300000102445)
                    ·
                      refine ⟨1724929914361612500038417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599813104964300000102445 1724929914361612500038417)
                      ·
                        rfl

theorem cell23_3359289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3359289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359289 prefixEnd_3359289 := by exact prefixLift 3359289
  have htrace : WordTrace (prefixWord ++ tailWord_3359289) baseStart_3359289 baseEnd_3359289 := by
    simpa [prefixWord, tailWord_3359289, baseEnd_3359289] using wordTrace_append hprefix tailTrace_3359289
  have hstable : (prefixWord ++ tailWord_3359289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359289).length < 2 ^ (prefixWord ++ tailWord_3359289).sum := by decide
  have hdescent : baseEnd_3359289 < baseStart_3359289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359296 : List Nat := [2, 1, 1, 2, 2, 2, 3, 5, 1, 4]
def baseStart_3359296 : Nat := 118140960795 + 3359296 * 2 ^ 59
def prefixEnd_3359296 : Nat := 4983230072969 + 3 ^ 40 * 3359296 * 2
def baseEnd_3359296 : Nat := 574977836242064657550295

theorem tailTrace_3359296 : CollatzResearch.WordTrace tailWord_3359296 prefixEnd_3359296 574977836242064657550295 := by
  unfold tailWord_3359296
  simp only [CollatzResearch.WordTrace]
  refine ⟨61261795418925894462780871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81682393891901192617041161 61261795418925894462780871)
  ·
    refine ⟨91892693128388841694171307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61261795418925894462780871 91892693128388841694171307)
    ·
      refine ⟨137839039692583262541256961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91892693128388841694171307 137839039692583262541256961)
      ·
        refine ⟨103379279769437446905942721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137839039692583262541256961 103379279769437446905942721)
        ·
          refine ⟨77534459827078085179457041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103379279769437446905942721 77534459827078085179457041)
          ·
            refine ⟨58150844870308563884592781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77534459827078085179457041 58150844870308563884592781)
            ·
              refine ⟨21806566826365711456722293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58150844870308563884592781 21806566826365711456722293)
              ·
                refine ⟨2044365639971785449067715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21806566826365711456722293 2044365639971785449067715)
                ·
                  refine ⟨3066548459957678173601573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044365639971785449067715 3066548459957678173601573)
                  ·
                    refine ⟨574977836242064657550295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066548459957678173601573 574977836242064657550295)
                    ·
                      rfl

theorem cell23_3359296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 5, 1, 4].length) (baseStart_3359296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359296 prefixEnd_3359296 := by exact prefixLift 3359296
  have htrace : WordTrace (prefixWord ++ tailWord_3359296) baseStart_3359296 baseEnd_3359296 := by
    simpa [prefixWord, tailWord_3359296, baseEnd_3359296] using wordTrace_append hprefix tailTrace_3359296
  have hstable : (prefixWord ++ tailWord_3359296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359296).length < 2 ^ (prefixWord ++ tailWord_3359296).sum := by decide
  have hdescent : baseEnd_3359296 < baseStart_3359296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359370 : List Nat := [3, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_3359370 : Nat := 118140960795 + 3359370 * 2 ^ 59
def prefixEnd_3359370 : Nat := 4983230072969 + 3 ^ 40 * 3359370 * 2
def baseEnd_3359370 : Nat := 1724971506294626683125545

theorem tailTrace_3359370 : CollatzResearch.WordTrace tailWord_3359370 prefixEnd_3359370 1724971506294626683125545 := by
  unfold tailWord_3359370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30631572459895924890938891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81684193226389133042503709 30631572459895924890938891)
  ·
    refine ⟨45947358689843887336408337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30631572459895924890938891 45947358689843887336408337)
    ·
      refine ⟨34460519017382915502306253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45947358689843887336408337 34460519017382915502306253)
      ·
        refine ⟨12922694631518593313364845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34460519017382915502306253 12922694631518593313364845)
        ·
          refine ⟨4846010486819472492511817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12922694631518593313364845 4846010486819472492511817)
          ·
            refine ⟨3634507865114604369383863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4846010486819472492511817 3634507865114604369383863)
            ·
              refine ⟨5451761797671906554075795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634507865114604369383863 5451761797671906554075795)
              ·
                refine ⟨8177642696507859831113693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451761797671906554075795 8177642696507859831113693)
                ·
                  refine ⟨3066616011190447436667635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8177642696507859831113693 3066616011190447436667635)
                  ·
                    refine ⟨4599924016785671155001453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3066616011190447436667635 4599924016785671155001453)
                    ·
                      refine ⟨1724971506294626683125545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599924016785671155001453 1724971506294626683125545)
                      ·
                        rfl

theorem cell23_3359370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_3359370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359370 prefixEnd_3359370 := by exact prefixLift 3359370
  have htrace : WordTrace (prefixWord ++ tailWord_3359370) baseStart_3359370 baseEnd_3359370 := by
    simpa [prefixWord, tailWord_3359370, baseEnd_3359370] using wordTrace_append hprefix tailTrace_3359370
  have hstable : (prefixWord ++ tailWord_3359370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359370).length < 2 ^ (prefixWord ++ tailWord_3359370).sum := by decide
  have hdescent : baseEnd_3359370 < baseStart_3359370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359379 : List Nat := [1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 3]
def baseStart_3359379 : Nat := 118140960795 + 3359379 * 2 ^ 59
def prefixEnd_3359379 : Nat := 4983230072969 + 3 ^ 40 * 3359379 * 2
def baseEnd_3359379 : Nat := 1724976127620517147913003

theorem tailTrace_3359379 : CollatzResearch.WordTrace tailWord_3359379 prefixEnd_3359379 1724976127620517147913003 := by
  unfold tailWord_3359379
  simp only [CollatzResearch.WordTrace]
  refine ⟨122526618096551094100833191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81684412064367396067222127 122526618096551094100833191)
  ·
    refine ⟨183789927144826641151249787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122526618096551094100833191 183789927144826641151249787)
    ·
      refine ⟨275684890717239961726874681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183789927144826641151249787 275684890717239961726874681)
      ·
        refine ⟨206763668037929971295156011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275684890717239961726874681 206763668037929971295156011)
        ·
          refine ⟨310145502056894956942734017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206763668037929971295156011 310145502056894956942734017)
          ·
            refine ⟨232609126542671217707050513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310145502056894956942734017 232609126542671217707050513)
            ·
              refine ⟨174456844907003413280287885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232609126542671217707050513 174456844907003413280287885)
              ·
                refine ⟨65421316840126279980107957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174456844907003413280287885 65421316840126279980107957)
                ·
                  refine ⟨6133248453761838748135121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65421316840126279980107957 6133248453761838748135121)
                  ·
                    refine ⟨4599936340321379061101341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6133248453761838748135121 4599936340321379061101341)
                    ·
                      refine ⟨1724976127620517147913003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599936340321379061101341 1724976127620517147913003)
                      ·
                        rfl

theorem cell23_3359379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 3].length) (baseStart_3359379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359379 prefixEnd_3359379 := by exact prefixLift 3359379
  have htrace : WordTrace (prefixWord ++ tailWord_3359379) baseStart_3359379 baseEnd_3359379 := by
    simpa [prefixWord, tailWord_3359379, baseEnd_3359379] using wordTrace_append hprefix tailTrace_3359379
  have hstable : (prefixWord ++ tailWord_3359379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359379).length < 2 ^ (prefixWord ++ tailWord_3359379).sum := by decide
  have hdescent : baseEnd_3359379 < baseStart_3359379 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359389 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_3359389 : Nat := 118140960795 + 3359389 * 2 ^ 59
def prefixEnd_3359389 : Nat := 4983230072969 + 3 ^ 40 * 3359389 * 2
def baseEnd_3359389 : Nat := 1724981262427062108787957

theorem tailTrace_3359389 : CollatzResearch.WordTrace tailWord_3359389 prefixEnd_3359389 1724981262427062108787957 := by
  unfold tailWord_3359389
  simp only [CollatzResearch.WordTrace]
  refine ⟨122526982826514865808697221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81684655217676577205798147 122526982826514865808697221)
  ·
    refine ⟨22973809279971537339130729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122526982826514865808697221 22973809279971537339130729)
    ·
      refine ⟨17230356959978653004348047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22973809279971537339130729 17230356959978653004348047)
      ·
        refine ⟨25845535439967979506522071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17230356959978653004348047 25845535439967979506522071)
        ·
          refine ⟨38768303159951969259783107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25845535439967979506522071 38768303159951969259783107)
          ·
            refine ⟨58152454739927953889674661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38768303159951969259783107 58152454739927953889674661)
            ·
              refine ⟨10903585263736491354313999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58152454739927953889674661 10903585263736491354313999)
              ·
                refine ⟨16355377895604737031470999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10903585263736491354313999 16355377895604737031470999)
                ·
                  refine ⟨24533066843407105547206499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16355377895604737031470999 24533066843407105547206499)
                  ·
                    refine ⟨36799600265110658320809749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24533066843407105547206499 36799600265110658320809749)
                    ·
                      refine ⟨1724981262427062108787957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36799600265110658320809749 1724981262427062108787957)
                      ·
                        rfl

theorem cell23_3359389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_3359389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359389 prefixEnd_3359389 := by exact prefixLift 3359389
  have htrace : WordTrace (prefixWord ++ tailWord_3359389) baseStart_3359389 baseEnd_3359389 := by
    simpa [prefixWord, tailWord_3359389, baseEnd_3359389] using wordTrace_append hprefix tailTrace_3359389
  have hstable : (prefixWord ++ tailWord_3359389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359389).length < 2 ^ (prefixWord ++ tailWord_3359389).sum := by decide
  have hdescent : baseEnd_3359389 < baseStart_3359389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359396 : List Nat := [2, 3, 1, 2, 2, 1, 3, 1, 3, 2, 3]
def baseStart_3359396 : Nat := 118140960795 + 3359396 * 2 ^ 59
def prefixEnd_3359396 : Nat := 4983230072969 + 3 ^ 40 * 3359396 * 2
def baseEnd_3359396 : Nat := 1724984856791643581400425

theorem tailTrace_3359396 : CollatzResearch.WordTrace tailWord_3359396 prefixEnd_3359396 1724984856791643581400425 := by
  unfold tailWord_3359396
  simp only [CollatzResearch.WordTrace]
  refine ⟨61263619068744753002101021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81684825424993004002801361 61263619068744753002101021)
  ·
    refine ⟨22973857150779282375787883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61263619068744753002101021 22973857150779282375787883)
    ·
      refine ⟨34460785726168923563681825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22973857150779282375787883 34460785726168923563681825)
      ·
        refine ⟨25845589294626692672761369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34460785726168923563681825 25845589294626692672761369)
        ·
          refine ⟨19384191970970019504571027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25845589294626692672761369 19384191970970019504571027)
          ·
            refine ⟨29076287956455029256856541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19384191970970019504571027 29076287956455029256856541)
            ·
              refine ⟨10903607983670635971321203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29076287956455029256856541 10903607983670635971321203)
              ·
                refine ⟨16355411975505953956981805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10903607983670635971321203 16355411975505953956981805)
                ·
                  refine ⟨6133279490814732733868177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16355411975505953956981805 6133279490814732733868177)
                  ·
                    refine ⟨4599959618111049550401133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6133279490814732733868177 4599959618111049550401133)
                    ·
                      refine ⟨1724984856791643581400425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4599959618111049550401133 1724984856791643581400425)
                      ·
                        rfl

theorem cell23_3359396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_3359396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359396 prefixEnd_3359396 := by exact prefixLift 3359396
  have htrace : WordTrace (prefixWord ++ tailWord_3359396) baseStart_3359396 baseEnd_3359396 := by
    simpa [prefixWord, tailWord_3359396, baseEnd_3359396] using wordTrace_append hprefix tailTrace_3359396
  have hstable : (prefixWord ++ tailWord_3359396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359396).length < 2 ^ (prefixWord ++ tailWord_3359396).sum := by decide
  have hdescent : baseEnd_3359396 < baseStart_3359396 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359410 : List Nat := [3, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_3359410 : Nat := 118140960795 + 3359410 * 2 ^ 59
def prefixEnd_3359410 : Nat := 4983230072969 + 3 ^ 40 * 3359410 * 2
def baseEnd_3359410 : Nat := 1724992045520806526625361

theorem tailTrace_3359410 : CollatzResearch.WordTrace tailWord_3359410 prefixEnd_3359410 1724992045520806526625361 := by
  unfold tailWord_3359410
  simp only [CollatzResearch.WordTrace]
  refine ⟨30631937189859696598802921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81685165839625857596807789 30631937189859696598802921)
  ·
    refine ⟨22973952892394772449102191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30631937189859696598802921 22973952892394772449102191)
    ·
      refine ⟨34460929338592158673653287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22973952892394772449102191 34460929338592158673653287)
      ·
        refine ⟨51691394007888238010479931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34460929338592158673653287 51691394007888238010479931)
        ·
          refine ⟨77537091011832357015719897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51691394007888238010479931 77537091011832357015719897)
          ·
            refine ⟨58152818258874267761789923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77537091011832357015719897 58152818258874267761789923)
            ·
              refine ⟨87229227388311401642684885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58152818258874267761789923 87229227388311401642684885)
              ·
                refine ⟨2044435016913548476000427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 87229227388311401642684885 2044435016913548476000427)
                ·
                  refine ⟨3066652525370322714000641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044435016913548476000427 3066652525370322714000641)
                  ·
                    refine ⟨2299989394027742035500481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3066652525370322714000641 2299989394027742035500481)
                    ·
                      refine ⟨1724992045520806526625361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2299989394027742035500481 1724992045520806526625361)
                      ·
                        rfl

theorem cell23_3359410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_3359410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359410 prefixEnd_3359410 := by exact prefixLift 3359410
  have htrace : WordTrace (prefixWord ++ tailWord_3359410) baseStart_3359410 baseEnd_3359410 := by
    simpa [prefixWord, tailWord_3359410, baseEnd_3359410] using wordTrace_append hprefix tailTrace_3359410
  have hstable : (prefixWord ++ tailWord_3359410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359410).length < 2 ^ (prefixWord ++ tailWord_3359410).sum := by decide
  have hdescent : baseEnd_3359410 < baseStart_3359410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359413 : List Nat := [1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3359413 : Nat := 118140960795 + 3359413 * 2 ^ 59
def prefixEnd_3359413 : Nat := 4983230072969 + 3 ^ 40 * 3359413 * 2
def baseEnd_3359413 : Nat := 1724993585962770014887847

theorem tailTrace_3359413 : CollatzResearch.WordTrace tailWord_3359413 prefixEnd_3359413 1724993585962770014887847 := by
  unfold tailWord_3359413
  simp only [CollatzResearch.WordTrace]
  refine ⟨122527858178427917907570893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81685238785618611938380595 122527858178427917907570893)
  ·
    refine ⟨45947946816910469215339085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122527858178427917907570893 45947946816910469215339085)
    ·
      refine ⟨17230480056341425955752157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45947946816910469215339085 17230480056341425955752157)
      ·
        refine ⟨6461430021128034733407059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17230480056341425955752157 6461430021128034733407059)
        ·
          refine ⟨9692145031692052100110589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461430021128034733407059 9692145031692052100110589)
          ·
            refine ⟨3634554386884519537541471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9692145031692052100110589 3634554386884519537541471)
            ·
              refine ⟨5451831580326779306312207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634554386884519537541471 5451831580326779306312207)
              ·
                refine ⟨8177747370490168959468311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5451831580326779306312207 8177747370490168959468311)
                ·
                  refine ⟨12266621055735253439202467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8177747370490168959468311 12266621055735253439202467)
                  ·
                    refine ⟨18399931583602880158803701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12266621055735253439202467 18399931583602880158803701)
                    ·
                      refine ⟨1724993585962770014887847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18399931583602880158803701 1724993585962770014887847)
                      ·
                        rfl

theorem cell23_3359413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3359413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359413 prefixEnd_3359413 := by exact prefixLift 3359413
  have htrace : WordTrace (prefixWord ++ tailWord_3359413) baseStart_3359413 baseEnd_3359413 := by
    simpa [prefixWord, tailWord_3359413, baseEnd_3359413] using wordTrace_append hprefix tailTrace_3359413
  have hstable : (prefixWord ++ tailWord_3359413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359413).length < 2 ^ (prefixWord ++ tailWord_3359413).sum := by decide
  have hdescent : baseEnd_3359413 < baseStart_3359413 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359449 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_3359449 : Nat := 118140960795 + 3359449 * 2 ^ 59
def prefixEnd_3359449 : Nat := 4983230072969 + 3 ^ 40 * 3359449 * 2
def baseEnd_3359449 : Nat := 1725012071266331874037681

theorem tailTrace_3359449 : CollatzResearch.WordTrace tailWord_3359449 prefixEnd_3359449 1725012071266331874037681 := by
  unfold tailWord_3359449
  simp only [CollatzResearch.WordTrace]
  refine ⟨122529171206297496055881401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81686114137531664037254267 122529171206297496055881401)
  ·
    refine ⟨91896878404723122041911051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122529171206297496055881401 91896878404723122041911051)
    ·
      refine ⟨137845317607084683062866577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91896878404723122041911051 137845317607084683062866577)
      ·
        refine ⟨103383988205313512297149933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137845317607084683062866577 103383988205313512297149933)
        ·
          refine ⟨38768995576992567111431225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103383988205313512297149933 38768995576992567111431225)
          ·
            refine ⟨29076746682744425333573419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38768995576992567111431225 29076746682744425333573419)
            ·
              refine ⟨43615120024116638000360129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29076746682744425333573419 43615120024116638000360129)
              ·
                refine ⟨32711340018087478500270097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43615120024116638000360129 32711340018087478500270097)
                ·
                  refine ⟨24533505013565608875202573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32711340018087478500270097 24533505013565608875202573)
                  ·
                    refine ⟨9200064380087103328200965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24533505013565608875202573 9200064380087103328200965)
                    ·
                      refine ⟨1725012071266331874037681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9200064380087103328200965 1725012071266331874037681)
                      ·
                        rfl

theorem cell23_3359449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_3359449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359449 prefixEnd_3359449 := by exact prefixLift 3359449
  have htrace : WordTrace (prefixWord ++ tailWord_3359449) baseStart_3359449 baseEnd_3359449 := by
    simpa [prefixWord, tailWord_3359449, baseEnd_3359449] using wordTrace_append hprefix tailTrace_3359449
  have hstable : (prefixWord ++ tailWord_3359449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359449).length < 2 ^ (prefixWord ++ tailWord_3359449).sum := by decide
  have hdescent : baseEnd_3359449 < baseStart_3359449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359470 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2]
def baseStart_3359470 : Nat := 118140960795 + 3359470 * 2 ^ 59
def prefixEnd_3359470 : Nat := 4983230072969 + 3 ^ 40 * 3359470 * 2
def baseEnd_3359470 : Nat := 1725022854360076291875085

theorem tailTrace_3359470 : CollatzResearch.WordTrace tailWord_3359470 prefixEnd_3359470 1725022854360076291875085 := by
  unfold tailWord_3359470
  simp only [CollatzResearch.WordTrace]
  refine ⟨15316242142402677080299483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81686624759480944428263909 15316242142402677080299483)
  ·
    refine ⟨22974363213604015620449225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15316242142402677080299483 22974363213604015620449225)
    ·
      refine ⟨17230772410203011715336919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22974363213604015620449225 17230772410203011715336919)
      ·
        refine ⟨25846158615304517573005379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17230772410203011715336919 25846158615304517573005379)
        ·
          refine ⟨38769237922956776359508069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25846158615304517573005379 38769237922956776359508069)
          ·
            refine ⟨7269232110554395567407763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38769237922956776359508069 7269232110554395567407763)
            ·
              refine ⟨10903848165831593351111645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7269232110554395567407763 10903848165831593351111645)
              ·
                refine ⟨4088943062186847506666867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10903848165831593351111645 4088943062186847506666867)
                ·
                  refine ⟨6133414593280271260000301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4088943062186847506666867 6133414593280271260000301)
                  ·
                    refine ⟨2300030472480101722500113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6133414593280271260000301 2300030472480101722500113)
                    ·
                      refine ⟨1725022854360076291875085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300030472480101722500113 1725022854360076291875085)
                      ·
                        rfl

theorem cell23_3359470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 1, 3, 2].length) (baseStart_3359470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359470 prefixEnd_3359470 := by exact prefixLift 3359470
  have htrace : WordTrace (prefixWord ++ tailWord_3359470) baseStart_3359470 baseEnd_3359470 := by
    simpa [prefixWord, tailWord_3359470, baseEnd_3359470] using wordTrace_append hprefix tailTrace_3359470
  have hstable : (prefixWord ++ tailWord_3359470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359470).length < 2 ^ (prefixWord ++ tailWord_3359470).sum := by decide
  have hdescent : baseEnd_3359470 < baseStart_3359470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359496 : List Nat := [2, 1, 3, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3359496 : Nat := 118140960795 + 3359496 * 2 ^ 59
def prefixEnd_3359496 : Nat := 4983230072969 + 3 ^ 40 * 3359496 * 2
def baseEnd_3359496 : Nat := 1725036204857093190149965

theorem tailTrace_3359496 : CollatzResearch.WordTrace tailWord_3359496 prefixEnd_3359496 1725036204857093190149965 := by
  unfold tailWord_3359496
  simp only [CollatzResearch.WordTrace]
  refine ⟨61265442718563611541421171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81687256958084815388561561 61265442718563611541421171)
  ·
    refine ⟨91898164077845417312131757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61265442718563611541421171 91898164077845417312131757)
    ·
      refine ⟨34461811529192031492049409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91898164077845417312131757 34461811529192031492049409)
      ·
        refine ⟨25846358646894023619037057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34461811529192031492049409 25846358646894023619037057)
        ·
          refine ⟨19384768985170517714277793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25846358646894023619037057 19384768985170517714277793)
          ·
            refine ⟨14538576738877888285708345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19384768985170517714277793 14538576738877888285708345)
            ·
              refine ⟨10903932554158416214281259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14538576738877888285708345 10903932554158416214281259)
              ·
                refine ⟨16355898831237624321421889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10903932554158416214281259 16355898831237624321421889)
                ·
                  refine ⟨12266924123428218241066417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16355898831237624321421889 12266924123428218241066417)
                  ·
                    refine ⟨9200193092571163680799813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12266924123428218241066417 9200193092571163680799813)
                    ·
                      refine ⟨1725036204857093190149965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9200193092571163680799813 1725036204857093190149965)
                      ·
                        rfl

theorem cell23_3359496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3359496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359496 prefixEnd_3359496 := by exact prefixLift 3359496
  have htrace : WordTrace (prefixWord ++ tailWord_3359496) baseStart_3359496 baseEnd_3359496 := by
    simpa [prefixWord, tailWord_3359496, baseEnd_3359496] using wordTrace_append hprefix tailTrace_3359496
  have hstable : (prefixWord ++ tailWord_3359496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359496).length < 2 ^ (prefixWord ++ tailWord_3359496).sum := by decide
  have hdescent : baseEnd_3359496 < baseStart_3359496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359529 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_3359529 : Nat := 118140960795 + 3359529 * 2 ^ 59
def prefixEnd_3359529 : Nat := 4983230072969 + 3 ^ 40 * 3359529 * 2
def baseEnd_3359529 : Nat := 1725053149718691561037313

theorem tailTrace_3359529 : CollatzResearch.WordTrace tailWord_3359529 prefixEnd_3359529 1725053149718691561037313 := by
  unfold tailWord_3359529
  simp only [CollatzResearch.WordTrace]
  refine ⟨122532089046007669718793641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81688059364005113145862427 122532089046007669718793641)
  ·
    refine ⟨91899066784505752289095231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122532089046007669718793641 91899066784505752289095231)
    ·
      refine ⟨137848600176758628433642847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91899066784505752289095231 137848600176758628433642847)
      ·
        refine ⟨206772900265137942650464271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137848600176758628433642847 206772900265137942650464271)
        ·
          refine ⟨310159350397706913975696407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206772900265137942650464271 310159350397706913975696407)
          ·
            refine ⟨465239025596560370963544611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310159350397706913975696407 465239025596560370963544611)
            ·
              refine ⟨697858538394840556445316917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465239025596560370963544611 697858538394840556445316917)
              ·
                refine ⟨65424237974516302166748461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 697858538394840556445316917 65424237974516302166748461)
                ·
                  refine ⟨24534089240443613312530673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65424237974516302166748461 24534089240443613312530673)
                  ·
                    refine ⟨18400566930332709984398005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24534089240443613312530673 18400566930332709984398005)
                    ·
                      refine ⟨1725053149718691561037313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18400566930332709984398005 1725053149718691561037313)
                      ·
                        rfl

theorem cell23_3359529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_3359529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359529 prefixEnd_3359529 := by exact prefixLift 3359529
  have htrace : WordTrace (prefixWord ++ tailWord_3359529) baseStart_3359529 baseEnd_3359529 := by
    simpa [prefixWord, tailWord_3359529, baseEnd_3359529] using wordTrace_append hprefix tailTrace_3359529
  have hstable : (prefixWord ++ tailWord_3359529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359529).length < 2 ^ (prefixWord ++ tailWord_3359529).sum := by decide
  have hdescent : baseEnd_3359529 < baseStart_3359529 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359540 : List Nat := [2, 5, 1, 1, 3, 2, 1, 1, 7]
def baseStart_3359540 : Nat := 118140960795 + 3359540 * 2 ^ 59
def prefixEnd_3359540 : Nat := 4983230072969 + 3 ^ 40 * 3359540 * 2
def baseEnd_3359540 : Nat := 191673199778432335333307

theorem tailTrace_3359540 : CollatzResearch.WordTrace tailWord_3359540 prefixEnd_3359540 191673199778432335333307 := by
  unfold tailWord_3359540
  simp only [CollatzResearch.WordTrace]
  refine ⟨61266245124483909298722037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81688326832645212398296049 61266245124483909298722037)
  ·
    refine ⟨5743710480420366496755191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61266245124483909298722037 5743710480420366496755191)
    ·
      refine ⟨8615565720630549745132787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5743710480420366496755191 8615565720630549745132787)
      ·
        refine ⟨12923348580945824617699181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8615565720630549745132787 12923348580945824617699181)
        ·
          refine ⟨4846255717854684231637193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12923348580945824617699181 4846255717854684231637193)
          ·
            refine ⟨3634691788391013173727895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4846255717854684231637193 3634691788391013173727895)
            ·
              refine ⟨5452037682586519760591843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634691788391013173727895 5452037682586519760591843)
              ·
                refine ⟨8178056523879779640887765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452037682586519760591843 8178056523879779640887765)
                ·
                  refine ⟨191673199778432335333307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8178056523879779640887765 191673199778432335333307)
                  ·
                    rfl

theorem cell23_3359540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_3359540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359540 prefixEnd_3359540 := by exact prefixLift 3359540
  have htrace : WordTrace (prefixWord ++ tailWord_3359540) baseStart_3359540 baseEnd_3359540 := by
    simpa [prefixWord, tailWord_3359540, baseEnd_3359540] using wordTrace_append hprefix tailTrace_3359540
  have hstable : (prefixWord ++ tailWord_3359540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359540).length < 2 ^ (prefixWord ++ tailWord_3359540).sum := by decide
  have hdescent : baseEnd_3359540 < baseStart_3359540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359573 : List Nat := [1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 4]
def baseStart_3359573 : Nat := 118140960795 + 3359573 * 2 ^ 59
def prefixEnd_3359573 : Nat := 4983230072969 + 3 ^ 40 * 3359573 * 2
def baseEnd_3359573 : Nat := 1725075742867489388887111

theorem tailTrace_3359573 : CollatzResearch.WordTrace tailWord_3359573 prefixEnd_3359573 1725075742867489388887111 := by
  unfold tailWord_3359573
  simp only [CollatzResearch.WordTrace]
  refine ⟨122533693857848265233395373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81689129238565510155596915 122533693857848265233395373)
  ·
    refine ⟨45950135196693099462523265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122533693857848265233395373 45950135196693099462523265)
    ·
      refine ⟨34462601397519824596892449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45950135196693099462523265 34462601397519824596892449)
      ·
        refine ⟨25846951048139868447669337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34462601397519824596892449 25846951048139868447669337)
        ·
          refine ⟨19385213286104901335752003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25846951048139868447669337 19385213286104901335752003)
          ·
            refine ⟨29077819929157352003628005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19385213286104901335752003 29077819929157352003628005)
            ·
              refine ⟨5452091236717003500680251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29077819929157352003628005 5452091236717003500680251)
              ·
                refine ⟨8178136855075505251020377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452091236717003500680251 8178136855075505251020377)
                ·
                  refine ⟨6133602641306628938265283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8178136855075505251020377 6133602641306628938265283)
                  ·
                    refine ⟨9200403961959943407397925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6133602641306628938265283 9200403961959943407397925)
                    ·
                      refine ⟨1725075742867489388887111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9200403961959943407397925 1725075742867489388887111)
                      ·
                        rfl

theorem cell23_3359573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_3359573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359573 prefixEnd_3359573 := by exact prefixLift 3359573
  have htrace : WordTrace (prefixWord ++ tailWord_3359573) baseStart_3359573 baseEnd_3359573 := by
    simpa [prefixWord, tailWord_3359573, baseEnd_3359573] using wordTrace_append hprefix tailTrace_3359573
  have hstable : (prefixWord ++ tailWord_3359573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359573).length < 2 ^ (prefixWord ++ tailWord_3359573).sum := by decide
  have hdescent : baseEnd_3359573 < baseStart_3359573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359576 : List Nat := [2, 1, 2, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_3359576 : Nat := 118140960795 + 3359576 * 2 ^ 59
def prefixEnd_3359576 : Nat := 4983230072969 + 3 ^ 40 * 3359576 * 2
def baseEnd_3359576 : Nat := 1725077283309452877149597

theorem tailTrace_3359576 : CollatzResearch.WordTrace tailWord_3359576 prefixEnd_3359576 1725077283309452877149597 := by
  unfold tailWord_3359576
  simp only [CollatzResearch.WordTrace]
  refine ⟨61266901638418698372877291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81689202184558264497169721 61266901638418698372877291)
  ·
    refine ⟨91900352457628047559315937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61266901638418698372877291 91900352457628047559315937)
    ·
      refine ⟨68925264343221035669486953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91900352457628047559315937 68925264343221035669486953)
      ·
        refine ⟨51693948257415776752115215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68925264343221035669486953 51693948257415776752115215)
        ·
          refine ⟨77540922386123665128172823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51693948257415776752115215 77540922386123665128172823)
          ·
            refine ⟨116311383579185497692259235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77540922386123665128172823 116311383579185497692259235)
            ·
              refine ⟨174467075368778246538388853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116311383579185497692259235 174467075368778246538388853)
              ·
                refine ⟨16356288315822960612973955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174467075368778246538388853 16356288315822960612973955)
                ·
                  refine ⟨24534432473734440919460933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16356288315822960612973955 24534432473734440919460933)
                  ·
                    refine ⟨4600206088825207672398925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24534432473734440919460933 4600206088825207672398925)
                    ·
                      refine ⟨1725077283309452877149597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4600206088825207672398925 1725077283309452877149597)
                      ·
                        rfl

theorem cell23_3359576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_3359576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359576 prefixEnd_3359576 := by exact prefixLift 3359576
  have htrace : WordTrace (prefixWord ++ tailWord_3359576) baseStart_3359576 baseEnd_3359576 := by
    simpa [prefixWord, tailWord_3359576, baseEnd_3359576] using wordTrace_append hprefix tailTrace_3359576
  have hstable : (prefixWord ++ tailWord_3359576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359576).length < 2 ^ (prefixWord ++ tailWord_3359576).sum := by decide
  have hdescent : baseEnd_3359576 < baseStart_3359576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359634 : List Nat := [3, 2, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3359634 : Nat := 118140960795 + 3359634 * 2 ^ 59
def prefixEnd_3359634 : Nat := 4983230072969 + 3 ^ 40 * 3359634 * 2
def baseEnd_3359634 : Nat := 575035688395804550074777

theorem tailTrace_3359634 : CollatzResearch.WordTrace tailWord_3359634 prefixEnd_3359634 575035688395804550074777 := by
  unfold tailWord_3359634
  simp only [CollatzResearch.WordTrace]
  refine ⟨30633979677656818162841489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81690612473751515100910637 30633979677656818162841489)
  ·
    refine ⟨22975484758242613622131117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30633979677656818162841489 22975484758242613622131117)
    ·
      refine ⟨8615806784340980108299169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22975484758242613622131117 8615806784340980108299169)
      ·
        refine ⟨6461855088255735081224377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8615806784340980108299169 6461855088255735081224377)
        ·
          refine ⟨4846391316191801310918283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6461855088255735081224377 4846391316191801310918283)
          ·
            refine ⟨7269586974287701966377425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846391316191801310918283 7269586974287701966377425)
            ·
              refine ⟨5452190230715776474783069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7269586974287701966377425 5452190230715776474783069)
              ·
                refine ⟨2044571336518416178043651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5452190230715776474783069 2044571336518416178043651)
                ·
                  refine ⟨3066857004777624267065477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044571336518416178043651 3066857004777624267065477)
                  ·
                    refine ⟨575035688395804550074777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3066857004777624267065477 575035688395804550074777)
                    ·
                      rfl

theorem cell23_3359634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3359634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359634 prefixEnd_3359634 := by exact prefixLift 3359634
  have htrace : WordTrace (prefixWord ++ tailWord_3359634) baseStart_3359634 baseEnd_3359634 := by
    simpa [prefixWord, tailWord_3359634, baseEnd_3359634] using wordTrace_append hprefix tailTrace_3359634
  have hstable : (prefixWord ++ tailWord_3359634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359634).length < 2 ^ (prefixWord ++ tailWord_3359634).sum := by decide
  have hdescent : baseEnd_3359634 < baseStart_3359634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359673 : List Nat := [1, 2, 1, 4, 2, 2, 3, 1, 1, 6]
def baseStart_3359673 : Nat := 118140960795 + 3359673 * 2 ^ 59
def prefixEnd_3359673 : Nat := 4983230072969 + 3 ^ 40 * 3359673 * 2
def baseEnd_3359673 : Nat := 575042363644312999212217

theorem tailTrace_3359673 : CollatzResearch.WordTrace tailWord_3359673 prefixEnd_3359673 575042363644312999212217 := by
  unfold tailWord_3359673
  simp only [CollatzResearch.WordTrace]
  refine ⟨122537341157485982312035673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81691560771657321541357115 122537341157485982312035673)
  ·
    refine ⟨91903005868114486734026755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122537341157485982312035673 91903005868114486734026755)
    ·
      refine ⟨137854508802171730101040133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91903005868114486734026755 137854508802171730101040133)
      ·
        refine ⟨25847720400407199393945025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137854508802171730101040133 25847720400407199393945025)
        ·
          refine ⟨19385790300305399545458769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25847720400407199393945025 19385790300305399545458769)
          ·
            refine ⟨14539342725229049659094077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19385790300305399545458769 14539342725229049659094077)
            ·
              refine ⟨5452253521960893622160279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14539342725229049659094077 5452253521960893622160279)
              ·
                refine ⟨8178380282941340433240419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452253521960893622160279 8178380282941340433240419)
                ·
                  refine ⟨12267570424412010649860629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178380282941340433240419 12267570424412010649860629)
                  ·
                    refine ⟨575042363644312999212217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12267570424412010649860629 575042363644312999212217)
                    ·
                      rfl

theorem cell23_3359673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_3359673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359673 prefixEnd_3359673 := by exact prefixLift 3359673
  have htrace : WordTrace (prefixWord ++ tailWord_3359673) baseStart_3359673 baseEnd_3359673 := by
    simpa [prefixWord, tailWord_3359673, baseEnd_3359673] using wordTrace_append hprefix tailTrace_3359673
  have hstable : (prefixWord ++ tailWord_3359673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359673).length < 2 ^ (prefixWord ++ tailWord_3359673).sum := by decide
  have hdescent : baseEnd_3359673 < baseStart_3359673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359680 : List Nat := [2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 4]
def baseStart_3359680 : Nat := 118140960795 + 3359680 * 2 ^ 59
def prefixEnd_3359680 : Nat := 4983230072969 + 3 ^ 40 * 3359680 * 2
def baseEnd_3359680 : Nat := 1725130685297520470249119

theorem tailTrace_3359680 : CollatzResearch.WordTrace tailWord_3359680 prefixEnd_3359680 1725130685297520470249119 := by
  unfold tailWord_3359680
  simp only [CollatzResearch.WordTrace]
  refine ⟨61268798234230311253770247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81691730978973748338360329 61268798234230311253770247)
  ·
    refine ⟨91903197351345466880655371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61268798234230311253770247 91903197351345466880655371)
    ·
      refine ⟨137854796027018200320983057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91903197351345466880655371 137854796027018200320983057)
      ·
        refine ⟨103391097020263650240737293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137854796027018200320983057 103391097020263650240737293)
        ·
          refine ⟨38771661382598868840276485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103391097020263650240737293 38771661382598868840276485)
          ·
            refine ⟨7269686509237287907551841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38771661382598868840276485 7269686509237287907551841)
            ·
              refine ⟨5452264881927965930663881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7269686509237287907551841 5452264881927965930663881)
              ·
                refine ⟨4089198661445974447997911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452264881927965930663881 4089198661445974447997911)
                ·
                  refine ⟨6133797992168961671996867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089198661445974447997911 6133797992168961671996867)
                  ·
                    refine ⟨9200696988253442507995301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6133797992168961671996867 9200696988253442507995301)
                    ·
                      refine ⟨1725130685297520470249119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9200696988253442507995301 1725130685297520470249119)
                      ·
                        rfl

theorem cell23_3359680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 2, 2, 1, 1, 4].length) (baseStart_3359680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359680 prefixEnd_3359680 := by exact prefixLift 3359680
  have htrace : WordTrace (prefixWord ++ tailWord_3359680) baseStart_3359680 baseEnd_3359680 := by
    simpa [prefixWord, tailWord_3359680, baseEnd_3359680] using wordTrace_append hprefix tailTrace_3359680
  have hstable : (prefixWord ++ tailWord_3359680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359680).length < 2 ^ (prefixWord ++ tailWord_3359680).sum := by decide
  have hdescent : baseEnd_3359680 < baseStart_3359680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359700 : List Nat := [2, 4, 1, 2, 1, 3, 2, 1, 1, 1, 5]
def baseStart_3359700 : Nat := 118140960795 + 3359700 * 2 ^ 59
def prefixEnd_3359700 : Nat := 4983230072969 + 3 ^ 40 * 3359700 * 2
def baseEnd_3359700 : Nat := 1725140954910610391999027

theorem tailTrace_3359700 : CollatzResearch.WordTrace tailWord_3359700 prefixEnd_3359700 1725140954910610391999027 := by
  unfold tailWord_3359700
  simp only [CollatzResearch.WordTrace]
  refine ⟨61269162964194082961634277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81692217285592110615512369 61269162964194082961634277)
  ·
    refine ⟨11487968055786390555306427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61269162964194082961634277 11487968055786390555306427)
    ·
      refine ⟨17231952083679585832959641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11487968055786390555306427 17231952083679585832959641)
      ·
        refine ⟨12923964062759689374719731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17231952083679585832959641 12923964062759689374719731)
        ·
          refine ⟨19385946094139534062079597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12923964062759689374719731 19385946094139534062079597)
          ·
            refine ⟨7269729785302325273279849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19385946094139534062079597 7269729785302325273279849)
            ·
              refine ⟨5452297338976743954959887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7269729785302325273279849 5452297338976743954959887)
              ·
                refine ⟨8178446008465115932439831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452297338976743954959887 8178446008465115932439831)
                ·
                  refine ⟨12267669012697673898659747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178446008465115932439831 12267669012697673898659747)
                  ·
                    refine ⟨18401503519046510847989621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12267669012697673898659747 18401503519046510847989621)
                    ·
                      refine ⟨1725140954910610391999027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18401503519046510847989621 1725140954910610391999027)
                      ·
                        rfl

theorem cell23_3359700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 1, 1, 1, 5].length) (baseStart_3359700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359700 prefixEnd_3359700 := by exact prefixLift 3359700
  have htrace : WordTrace (prefixWord ++ tailWord_3359700) baseStart_3359700 baseEnd_3359700 := by
    simpa [prefixWord, tailWord_3359700, baseEnd_3359700] using wordTrace_append hprefix tailTrace_3359700
  have hstable : (prefixWord ++ tailWord_3359700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359700).length < 2 ^ (prefixWord ++ tailWord_3359700).sum := by decide
  have hdescent : baseEnd_3359700 < baseStart_3359700 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359723 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 1, 9, 2]
def baseStart_3359723 : Nat := 118140960795 + 3359723 * 2 ^ 59
def prefixEnd_3359723 : Nat := 4983230072969 + 3 ^ 40 * 3359723 * 2
def baseEnd_3359723 : Nat := 1725152764965663802011421

theorem tailTrace_3359723 : CollatzResearch.WordTrace tailWord_3359723 prefixEnd_3359723 1725152764965663802011421 := by
  unfold tailWord_3359723
  simp only [CollatzResearch.WordTrace]
  refine ⟨122539164807304840851355823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81692776538203227234237215 122539164807304840851355823)
  ·
    refine ⟨183808747210957261277033735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122539164807304840851355823 183808747210957261277033735)
    ·
      refine ⟨275713120816435891915550603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183808747210957261277033735 275713120816435891915550603)
      ·
        refine ⟨413569681224653837873325905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275713120816435891915550603 413569681224653837873325905)
        ·
          refine ⟨310177260918490378404994429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413569681224653837873325905 310177260918490378404994429)
          ·
            refine ⟨116316472844433891901872911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310177260918490378404994429 116316472844433891901872911)
            ·
              refine ⟨174474709266650837852809367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116316472844433891901872911 174474709266650837852809367)
              ·
                refine ⟨261712063899976256779214051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174474709266650837852809367 261712063899976256779214051)
                ·
                  refine ⟨392568095849964385168821077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 261712063899976256779214051 392568095849964385168821077)
                  ·
                    refine ⟨2300203686620885069348561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 392568095849964385168821077 2300203686620885069348561)
                    ·
                      refine ⟨1725152764965663802011421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300203686620885069348561 1725152764965663802011421)
                      ·
                        rfl

theorem cell23_3359723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 9, 2].length) (baseStart_3359723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359723 prefixEnd_3359723 := by exact prefixLift 3359723
  have htrace : WordTrace (prefixWord ++ tailWord_3359723) baseStart_3359723 baseEnd_3359723 := by
    simpa [prefixWord, tailWord_3359723, baseEnd_3359723] using wordTrace_append hprefix tailTrace_3359723
  have hstable : (prefixWord ++ tailWord_3359723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359723).length < 2 ^ (prefixWord ++ tailWord_3359723).sum := by decide
  have hdescent : baseEnd_3359723 < baseStart_3359723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359734 : List Nat := [5, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3]
def baseStart_3359734 : Nat := 118140960795 + 3359734 * 2 ^ 59
def prefixEnd_3359734 : Nat := 4983230072969 + 3 ^ 40 * 3359734 * 2
def baseEnd_3359734 : Nat := 1725158413252863258973871

theorem tailTrace_3359734 : CollatzResearch.WordTrace tailWord_3359734 prefixEnd_3359734 1725158413252863258973871 := by
  unfold tailWord_3359734
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658722875641561858125391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81693044006843326486670837 7658722875641561858125391)
  ·
    refine ⟨11488084313462342787188087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7658722875641561858125391 11488084313462342787188087)
    ·
      refine ⟨17232126470193514180782131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11488084313462342787188087 17232126470193514180782131)
      ·
        refine ⟨25848189705290271271173197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17232126470193514180782131 25848189705290271271173197)
        ·
          refine ⟨9693071139483851726689949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25848189705290271271173197 9693071139483851726689949)
          ·
            refine ⟨3634901677306444397508731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9693071139483851726689949 3634901677306444397508731)
            ·
              refine ⟨5452352515959666596263097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634901677306444397508731 5452352515959666596263097)
              ·
                refine ⟨4089264386969749947197323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452352515959666596263097 4089264386969749947197323)
                ·
                  refine ⟨6133896580454624920795985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089264386969749947197323 6133896580454624920795985)
                  ·
                    refine ⟨4600422435340968690596989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6133896580454624920795985 4600422435340968690596989)
                    ·
                      refine ⟨1725158413252863258973871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4600422435340968690596989 1725158413252863258973871)
                      ·
                        rfl

theorem cell23_3359734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3].length) (baseStart_3359734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359734 prefixEnd_3359734 := by exact prefixLift 3359734
  have htrace : WordTrace (prefixWord ++ tailWord_3359734) baseStart_3359734 baseEnd_3359734 := by
    simpa [prefixWord, tailWord_3359734, baseEnd_3359734] using wordTrace_append hprefix tailTrace_3359734
  have hstable : (prefixWord ++ tailWord_3359734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359734).length < 2 ^ (prefixWord ++ tailWord_3359734).sum := by decide
  have hdescent : baseEnd_3359734 < baseStart_3359734 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359736 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_3359736 : Nat := 118140960795 + 3359736 * 2 ^ 59
def prefixEnd_3359736 : Nat := 4983230072969 + 3 ^ 40 * 3359736 * 2
def baseEnd_3359736 : Nat := 1725159440214172251148861

theorem tailTrace_3359736 : CollatzResearch.WordTrace tailWord_3359736 prefixEnd_3359736 1725159440214172251148861 := by
  unfold tailWord_3359736
  simp only [CollatzResearch.WordTrace]
  refine ⟨61269819478128872035789531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81693092637505162714386041 61269819478128872035789531)
  ·
    refine ⟨91904729217193308053684297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61269819478128872035789531 91904729217193308053684297)
    ·
      refine ⟨68928546912894981040263223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91904729217193308053684297 68928546912894981040263223)
      ·
        refine ⟨103392820369342471560394835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68928546912894981040263223 103392820369342471560394835)
        ·
          refine ⟨155089230554013707340592253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103392820369342471560394835 155089230554013707340592253)
          ·
            refine ⟨58158461457755140252722095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155089230554013707340592253 58158461457755140252722095)
            ·
              refine ⟨87237692186632710379083143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58158461457755140252722095 87237692186632710379083143)
              ·
                refine ⟨130856538279949065568624715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87237692186632710379083143 130856538279949065568624715)
                ·
                  refine ⟨196284807419923598352937073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130856538279949065568624715 196284807419923598352937073)
                  ·
                    refine ⟨147213605564942698764702805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 196284807419923598352937073 147213605564942698764702805)
                    ·
                      refine ⟨1725159440214172251148861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 147213605564942698764702805 1725159440214172251148861)
                      ·
                        rfl

theorem cell23_3359736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_3359736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359736 prefixEnd_3359736 := by exact prefixLift 3359736
  have htrace : WordTrace (prefixWord ++ tailWord_3359736) baseStart_3359736 baseEnd_3359736 := by
    simpa [prefixWord, tailWord_3359736, baseEnd_3359736] using wordTrace_append hprefix tailTrace_3359736
  have hstable : (prefixWord ++ tailWord_3359736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359736).length < 2 ^ (prefixWord ++ tailWord_3359736).sum := by decide
  have hdescent : baseEnd_3359736 < baseStart_3359736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359770 : List Nat := [3, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2]
def baseStart_3359770 : Nat := 118140960795 + 3359770 * 2 ^ 59
def prefixEnd_3359770 : Nat := 4983230072969 + 3 ^ 40 * 3359770 * 2
def baseEnd_3359770 : Nat := 1725176898556425118123705

theorem tailTrace_3359770 : CollatzResearch.WordTrace tailWord_3359770 prefixEnd_3359770 1725176898556425118123705 := by
  unfold tailWord_3359770
  simp only [CollatzResearch.WordTrace]
  refine ⟨30635219759533641969579191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81693919358756378585544509 30635219759533641969579191)
  ·
    refine ⟨45952829639300462954368787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30635219759533641969579191 45952829639300462954368787)
    ·
      refine ⟨68929244458950694431553181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45952829639300462954368787 68929244458950694431553181)
      ·
        refine ⟨25848466672106510411832443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68929244458950694431553181 25848466672106510411832443)
        ·
          refine ⟨38772700008159765617748665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25848466672106510411832443 38772700008159765617748665)
          ·
            refine ⟨29079525006119824213311499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38772700008159765617748665 29079525006119824213311499)
            ·
              refine ⟨43619287509179736319967249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29079525006119824213311499 43619287509179736319967249)
              ·
                refine ⟨32714465631884802239975437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43619287509179736319967249 32714465631884802239975437)
                ·
                  refine ⟨12267924611956800839990789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32714465631884802239975437 12267924611956800839990789)
                  ·
                    refine ⟨2300235864741900157498273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12267924611956800839990789 2300235864741900157498273)
                    ·
                      refine ⟨1725176898556425118123705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300235864741900157498273 1725176898556425118123705)
                      ·
                        rfl

theorem cell23_3359770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_3359770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359770 prefixEnd_3359770 := by exact prefixLift 3359770
  have htrace : WordTrace (prefixWord ++ tailWord_3359770) baseStart_3359770 baseEnd_3359770 := by
    simpa [prefixWord, tailWord_3359770, baseEnd_3359770] using wordTrace_append hprefix tailTrace_3359770
  have hstable : (prefixWord ++ tailWord_3359770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359770).length < 2 ^ (prefixWord ++ tailWord_3359770).sum := by decide
  have hdescent : baseEnd_3359770 < baseStart_3359770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359780 : List Nat := [2, 3, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_3359780 : Nat := 118140960795 + 3359780 * 2 ^ 59
def prefixEnd_3359780 : Nat := 4983230072969 + 3 ^ 40 * 3359780 * 2
def baseEnd_3359780 : Nat := 575060677787656692999553

theorem tailTrace_3359780 : CollatzResearch.WordTrace tailWord_3359780 prefixEnd_3359780 575060677787656692999553 := by
  unfold tailWord_3359780
  simp only [CollatzResearch.WordTrace]
  refine ⟨61270621884049169793090397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81694162512065559724120529 61270621884049169793090397)
  ·
    refine ⟨22976483206518438672408899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61270621884049169793090397 22976483206518438672408899)
    ·
      refine ⟨34464724809777658008613349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22976483206518438672408899 34464724809777658008613349)
      ·
        refine ⟨6462135901833310876615003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34464724809777658008613349 6462135901833310876615003)
        ·
          refine ⟨9693203852749966314922505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462135901833310876615003 9693203852749966314922505)
          ·
            refine ⟨7269902889562474736191879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9693203852749966314922505 7269902889562474736191879)
            ·
              refine ⟨10904854334343712104287819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7269902889562474736191879 10904854334343712104287819)
              ·
                refine ⟨16357281501515568156431729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10904854334343712104287819 16357281501515568156431729)
                ·
                  refine ⟨12267961126136676117323797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16357281501515568156431729 12267961126136676117323797)
                  ·
                    refine ⟨575060677787656692999553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12267961126136676117323797 575060677787656692999553)
                    ·
                      rfl

theorem cell23_3359780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_3359780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359780 prefixEnd_3359780 := by exact prefixLift 3359780
  have htrace : WordTrace (prefixWord ++ tailWord_3359780) baseStart_3359780 baseEnd_3359780 := by
    simpa [prefixWord, tailWord_3359780, baseEnd_3359780] using wordTrace_append hprefix tailTrace_3359780
  have hstable : (prefixWord ++ tailWord_3359780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359780).length < 2 ^ (prefixWord ++ tailWord_3359780).sum := by decide
  have hdescent : baseEnd_3359780 < baseStart_3359780 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359787 : List Nat := [1, 1, 1, 1, 2, 1, 5, 5, 2, 2, 2]
def baseStart_3359787 : Nat := 118140960795 + 3359787 * 2 ^ 59
def prefixEnd_3359787 : Nat := 4983230072969 + 3 ^ 40 * 3359787 * 2
def baseEnd_3359787 : Nat := 1725185627727551551611127

theorem tailTrace_3359787 : CollatzResearch.WordTrace tailWord_3359787 prefixEnd_3359787 1725185627727551551611127 := by
  unfold tailWord_3359787
  simp only [CollatzResearch.WordTrace]
  refine ⟨122541499079072979781685615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81694332719381986521123743 122541499079072979781685615)
  ·
    refine ⟨183812248618609469672528423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122541499079072979781685615 183812248618609469672528423)
    ·
      refine ⟨275718372927914204508792635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183812248618609469672528423 275718372927914204508792635)
      ·
        refine ⟨413577559391871306763188953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275718372927914204508792635 413577559391871306763188953)
        ·
          refine ⟨310183169543903480072391715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413577559391871306763188953 310183169543903480072391715)
          ·
            refine ⟨465274754315855220108587573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310183169543903480072391715 465274754315855220108587573)
            ·
              refine ⟨43619508217111426885180085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 465274754315855220108587573 43619508217111426885180085)
              ·
                refine ⟨4089328895354196270485633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43619508217111426885180085 4089328895354196270485633)
                ·
                  refine ⟨3066996671515647202864225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4089328895354196270485633 3066996671515647202864225)
                  ·
                    refine ⟨2300247503636735402148169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3066996671515647202864225 2300247503636735402148169)
                    ·
                      refine ⟨1725185627727551551611127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300247503636735402148169 1725185627727551551611127)
                      ·
                        rfl

theorem cell23_3359787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 5, 2, 2, 2].length) (baseStart_3359787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359787 prefixEnd_3359787 := by exact prefixLift 3359787
  have htrace : WordTrace (prefixWord ++ tailWord_3359787) baseStart_3359787 baseEnd_3359787 := by
    simpa [prefixWord, tailWord_3359787, baseEnd_3359787] using wordTrace_append hprefix tailTrace_3359787
  have hstable : (prefixWord ++ tailWord_3359787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359787).length < 2 ^ (prefixWord ++ tailWord_3359787).sum := by decide
  have hdescent : baseEnd_3359787 < baseStart_3359787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359790 : List Nat := [4, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3]
def baseStart_3359790 : Nat := 118140960795 + 3359790 * 2 ^ 59
def prefixEnd_3359790 : Nat := 4983230072969 + 3 ^ 40 * 3359790 * 2
def baseEnd_3359790 : Nat := 1725187168169515039873613

theorem tailTrace_3359790 : CollatzResearch.WordTrace tailWord_3359790 prefixEnd_3359790 1725187168169515039873613 := by
  unfold tailWord_3359790
  simp only [CollatzResearch.WordTrace]
  refine ⟨15317701062257763911755603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81694405665374740862696549 15317701062257763911755603)
  ·
    refine ⟨22976551593386645867633405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15317701062257763911755603 22976551593386645867633405)
    ·
      refine ⟨8616206847519992200362527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22976551593386645867633405 8616206847519992200362527)
      ·
        refine ⟨12924310271279988300543791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8616206847519992200362527 12924310271279988300543791)
        ·
          refine ⟨19386465406919982450815687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12924310271279988300543791 19386465406919982450815687)
          ·
            refine ⟨29079698110379973676223531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19386465406919982450815687 29079698110379973676223531)
            ·
              refine ⟨43619547165569960514335297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29079698110379973676223531 43619547165569960514335297)
              ·
                refine ⟨32714660374177470385751473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43619547165569960514335297 32714660374177470385751473)
                ·
                  refine ⟨24535995280633102789313605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32714660374177470385751473 24535995280633102789313605)
                  ·
                    refine ⟨4600499115118706772996301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24535995280633102789313605 4600499115118706772996301)
                    ·
                      refine ⟨1725187168169515039873613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4600499115118706772996301 1725187168169515039873613)
                      ·
                        rfl

theorem cell23_3359790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_3359790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359790 prefixEnd_3359790 := by exact prefixLift 3359790
  have htrace : WordTrace (prefixWord ++ tailWord_3359790) baseStart_3359790 baseEnd_3359790 := by
    simpa [prefixWord, tailWord_3359790, baseEnd_3359790] using wordTrace_append hprefix tailTrace_3359790
  have hstable : (prefixWord ++ tailWord_3359790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359790).length < 2 ^ (prefixWord ++ tailWord_3359790).sum := by decide
  have hdescent : baseEnd_3359790 < baseStart_3359790 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359793 : List Nat := [1, 2, 2, 3, 1, 2, 3, 2, 7]
def baseStart_3359793 : Nat := 118140960795 + 3359793 * 2 ^ 59
def prefixEnd_3359793 : Nat := 4983230072969 + 3 ^ 40 * 3359793 * 2
def baseEnd_3359793 : Nat := 191687634290164280904011

theorem tailTrace_3359793 : CollatzResearch.WordTrace tailWord_3359793 prefixEnd_3359793 191687634290164280904011 := by
  unfold tailWord_3359793
  simp only [CollatzResearch.WordTrace]
  refine ⟨122541717917051242806404033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81694478611367495204269355 122541717917051242806404033)
  ·
    refine ⟨91906288437788432104803025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122541717917051242806404033 91906288437788432104803025)
    ·
      refine ⟨68929716328341324078602269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91906288437788432104803025 68929716328341324078602269)
      ·
        refine ⟨25848643623127996529475851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68929716328341324078602269 25848643623127996529475851)
        ·
          refine ⟨38772965434691994794213777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25848643623127996529475851 38772965434691994794213777)
          ·
            refine ⟨29079724076018996095660333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38772965434691994794213777 29079724076018996095660333)
            ·
              refine ⟨10904896528507123535872625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29079724076018996095660333 10904896528507123535872625)
              ·
                refine ⟨8178672396380342651904469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10904896528507123535872625 8178672396380342651904469)
                ·
                  refine ⟨191687634290164280904011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8178672396380342651904469 191687634290164280904011)
                  ·
                    rfl

theorem cell23_3359793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 2, 7].length) (baseStart_3359793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359793 prefixEnd_3359793 := by exact prefixLift 3359793
  have htrace : WordTrace (prefixWord ++ tailWord_3359793) baseStart_3359793 baseEnd_3359793 := by
    simpa [prefixWord, tailWord_3359793, baseEnd_3359793] using wordTrace_append hprefix tailTrace_3359793
  have hstable : (prefixWord ++ tailWord_3359793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359793).length < 2 ^ (prefixWord ++ tailWord_3359793).sum := by decide
  have hdescent : baseEnd_3359793 < baseStart_3359793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359803 : List Nat := [1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 3]
def baseStart_3359803 : Nat := 118140960795 + 3359803 * 2 ^ 59
def prefixEnd_3359803 : Nat := 4983230072969 + 3 ^ 40 * 3359803 * 2
def baseEnd_3359803 : Nat := 1725193843418023489011053

theorem tailTrace_3359803 : CollatzResearch.WordTrace tailWord_3359803 prefixEnd_3359803 1725193843418023489011053 := by
  unfold tailWord_3359803
  simp only [CollatzResearch.WordTrace]
  refine ⟨122542082647015014514268063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81694721764676676342845375 122542082647015014514268063)
  ·
    refine ⟨183813123970522521771402095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122542082647015014514268063 183813123970522521771402095)
    ·
      refine ⟨275719685955783782657103143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183813123970522521771402095 275719685955783782657103143)
      ·
        refine ⟨413579528933675673985654715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275719685955783782657103143 413579528933675673985654715)
        ·
          refine ⟨620369293400513510978482073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413579528933675673985654715 620369293400513510978482073)
          ·
            refine ⟨465276970050385133233861555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620369293400513510978482073 465276970050385133233861555)
            ·
              refine ⟨697915455075577699850792333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465276970050385133233861555 697915455075577699850792333)
              ·
                refine ⟨261718295653341637444047125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 697915455075577699850792333 261718295653341637444047125)
                ·
                  refine ⟨12268045108750389255189709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261718295653341637444047125 12268045108750389255189709)
                  ·
                    refine ⟨4600516915781395970696141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12268045108750389255189709 4600516915781395970696141)
                    ·
                      refine ⟨1725193843418023489011053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4600516915781395970696141 1725193843418023489011053)
                      ·
                        rfl

theorem cell23_3359803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 6, 3, 3].length) (baseStart_3359803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359803 prefixEnd_3359803 := by exact prefixLift 3359803
  have htrace : WordTrace (prefixWord ++ tailWord_3359803) baseStart_3359803 baseEnd_3359803 := by
    simpa [prefixWord, tailWord_3359803, baseEnd_3359803] using wordTrace_append hprefix tailTrace_3359803
  have hstable : (prefixWord ++ tailWord_3359803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359803).length < 2 ^ (prefixWord ++ tailWord_3359803).sum := by decide
  have hdescent : baseEnd_3359803 < baseStart_3359803 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359821 : List Nat := [1, 6, 1, 1, 1, 2, 3, 2, 2, 2, 2]
def baseStart_3359821 : Nat := 118140960795 + 3359821 * 2 ^ 59
def prefixEnd_3359821 : Nat := 4983230072969 + 3 ^ 40 * 3359821 * 2
def baseEnd_3359821 : Nat := 1725203086069804418585971

theorem tailTrace_3359821 : CollatzResearch.WordTrace tailWord_3359821 prefixEnd_3359821 1725203086069804418585971 := by
  unfold tailWord_3359821
  simp only [CollatzResearch.WordTrace]
  refine ⟨122542739160949803588423317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81695159440633202392282211 122542739160949803588423317)
  ·
    refine ⟨5744190898169522043207343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122542739160949803588423317 5744190898169522043207343)
    ·
      refine ⟨8616286347254283064811015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5744190898169522043207343 8616286347254283064811015)
      ·
        refine ⟨12924429520881424597216523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8616286347254283064811015 12924429520881424597216523)
        ·
          refine ⟨19386644281322136895824785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12924429520881424597216523 19386644281322136895824785)
          ·
            refine ⟨14539983210991602671868589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19386644281322136895824785 14539983210991602671868589)
            ·
              refine ⟨5452493704121851001950721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14539983210991602671868589 5452493704121851001950721)
              ·
                refine ⟨4089370278091388251463041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452493704121851001950721 4089370278091388251463041)
                ·
                  refine ⟨3067027708568541188597281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4089370278091388251463041 3067027708568541188597281)
                  ·
                    refine ⟨2300270781426405891447961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3067027708568541188597281 2300270781426405891447961)
                    ·
                      refine ⟨1725203086069804418585971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300270781426405891447961 1725203086069804418585971)
                      ·
                        rfl

theorem cell23_3359821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 3, 2, 2, 2, 2].length) (baseStart_3359821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359821 prefixEnd_3359821 := by exact prefixLift 3359821
  have htrace : WordTrace (prefixWord ++ tailWord_3359821) baseStart_3359821 baseEnd_3359821 := by
    simpa [prefixWord, tailWord_3359821, baseEnd_3359821] using wordTrace_append hprefix tailTrace_3359821
  have hstable : (prefixWord ++ tailWord_3359821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359821).length < 2 ^ (prefixWord ++ tailWord_3359821).sum := by decide
  have hdescent : baseEnd_3359821 < baseStart_3359821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359838 : List Nat := [4, 4, 1, 1, 1, 3, 1, 1, 1, 4, 2]
def baseStart_3359838 : Nat := 118140960795 + 3359838 * 2 ^ 59
def prefixEnd_3359838 : Nat := 4983230072969 + 3 ^ 40 * 3359838 * 2
def baseEnd_3359838 : Nat := 1725211815240930852073393

theorem tailTrace_3359838 : CollatzResearch.WordTrace tailWord_3359838 prefixEnd_3359838 1725211815240930852073393 := by
  unfold tailWord_3359838
  simp only [CollatzResearch.WordTrace]
  refine ⟨15317919900236026936474021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81695572801258810327861445 15317919900236026936474021)
  ·
    refine ⟨2872109981294255050588879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15317919900236026936474021 2872109981294255050588879)
    ·
      refine ⟨4308164971941382575883319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872109981294255050588879 4308164971941382575883319)
      ·
        refine ⟨6462247457912073863824979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308164971941382575883319 6462247457912073863824979)
        ·
          refine ⟨9693371186868110795737469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462247457912073863824979 9693371186868110795737469)
          ·
            refine ⟨3635014195075541548401551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9693371186868110795737469 3635014195075541548401551)
            ·
              refine ⟨5452521292613312322602327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635014195075541548401551 5452521292613312322602327)
              ·
                refine ⟨8178781938919968483903491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452521292613312322602327 8178781938919968483903491)
                ·
                  refine ⟨12268172908379952725855237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8178781938919968483903491 12268172908379952725855237)
                  ·
                    refine ⟨2300282420321241136097857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12268172908379952725855237 2300282420321241136097857)
                    ·
                      refine ⟨1725211815240930852073393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300282420321241136097857 1725211815240930852073393)
                      ·
                        rfl

theorem cell23_3359838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_3359838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359838 prefixEnd_3359838 := by exact prefixLift 3359838
  have htrace : WordTrace (prefixWord ++ tailWord_3359838) baseStart_3359838 baseEnd_3359838 := by
    simpa [prefixWord, tailWord_3359838, baseEnd_3359838] using wordTrace_append hprefix tailTrace_3359838
  have hstable : (prefixWord ++ tailWord_3359838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359838).length < 2 ^ (prefixWord ++ tailWord_3359838).sum := by decide
  have hdescent : baseEnd_3359838 < baseStart_3359838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359861 : List Nat := [1, 3, 4, 3, 1, 2, 1, 3, 5]
def baseStart_3359861 : Nat := 118140960795 + 3359861 * 2 ^ 59
def prefixEnd_3359861 : Nat := 4983230072969 + 3 ^ 40 * 3359861 * 2
def baseEnd_3359861 : Nat := 191691513921776029120643

theorem tailTrace_3359861 : CollatzResearch.WordTrace tailWord_3359861 prefixEnd_3359861 191691513921776029120643 := by
  unfold tailWord_3359861
  simp only [CollatzResearch.WordTrace]
  refine ⟨122544198080804890419879437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81696132053869926946586291 122544198080804890419879437)
  ·
    refine ⟨45954074280301833907454789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122544198080804890419879437 45954074280301833907454789)
    ·
      refine ⟨8616388927556593857647773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45954074280301833907454789 8616388927556593857647773)
      ·
        refine ⟨3231145847833722696617915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8616388927556593857647773 3231145847833722696617915)
        ·
          refine ⟨4846718771750584044926873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231145847833722696617915 4846718771750584044926873)
          ·
            refine ⟨3635039078812938033695155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4846718771750584044926873 3635039078812938033695155)
            ·
              refine ⟨5452558618219407050542733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635039078812938033695155 5452558618219407050542733)
              ·
                refine ⟨2044709481832277643953525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5452558618219407050542733 2044709481832277643953525)
                ·
                  refine ⟨191691513921776029120643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2044709481832277643953525 191691513921776029120643)
                  ·
                    rfl

theorem cell23_3359861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_3359861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359861 prefixEnd_3359861 := by exact prefixLift 3359861
  have htrace : WordTrace (prefixWord ++ tailWord_3359861) baseStart_3359861 baseEnd_3359861 := by
    simpa [prefixWord, tailWord_3359861, baseEnd_3359861] using wordTrace_append hprefix tailTrace_3359861
  have hstable : (prefixWord ++ tailWord_3359861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359861).length < 2 ^ (prefixWord ++ tailWord_3359861).sum := by decide
  have hdescent : baseEnd_3359861 < baseStart_3359861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359877 : List Nat := [1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 4]
def baseStart_3359877 : Nat := 118140960795 + 3359877 * 2 ^ 59
def prefixEnd_3359877 : Nat := 4983230072969 + 3 ^ 40 * 3359877 * 2
def baseEnd_3359877 : Nat := 1725231840986456199485713

theorem tailTrace_3359877 : CollatzResearch.WordTrace tailWord_3359877 prefixEnd_3359877 1725231840986456199485713 := by
  unfold tailWord_3359877
  simp only [CollatzResearch.WordTrace]
  refine ⟨122544781648746925152461885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81696521099164616768307923 122544781648746925152461885)
  ·
    refine ⟨45954293118280096932173207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122544781648746925152461885 45954293118280096932173207)
    ·
      refine ⟨68931439677420145398259811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45954293118280096932173207 68931439677420145398259811)
      ·
        refine ⟨103397159516130218097389717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68931439677420145398259811 103397159516130218097389717)
        ·
          refine ⟨4846741852318603973315143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103397159516130218097389717 4846741852318603973315143)
          ·
            refine ⟨7270112778477905959972715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846741852318603973315143 7270112778477905959972715)
            ·
              refine ⟨10905169167716858939959073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7270112778477905959972715 10905169167716858939959073)
              ·
                refine ⟨8178876875787644204969305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10905169167716858939959073 8178876875787644204969305)
                ·
                  refine ⟨6134157656840733153726979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8178876875787644204969305 6134157656840733153726979)
                  ·
                    refine ⟨9201236485261099730590469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6134157656840733153726979 9201236485261099730590469)
                    ·
                      refine ⟨1725231840986456199485713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9201236485261099730590469 1725231840986456199485713)
                      ·
                        rfl

theorem cell23_3359877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 2, 2, 1, 4].length) (baseStart_3359877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359877 prefixEnd_3359877 := by exact prefixLift 3359877
  have htrace : WordTrace (prefixWord ++ tailWord_3359877) baseStart_3359877 baseEnd_3359877 := by
    simpa [prefixWord, tailWord_3359877, baseEnd_3359877] using wordTrace_append hprefix tailTrace_3359877
  have hstable : (prefixWord ++ tailWord_3359877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359877).length < 2 ^ (prefixWord ++ tailWord_3359877).sum := by decide
  have hdescent : baseEnd_3359877 < baseStart_3359877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359914 : List Nat := [3, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_3359914 : Nat := 118140960795 + 3359914 * 2 ^ 59
def prefixEnd_3359914 : Nat := 4983230072969 + 3 ^ 40 * 3359914 * 2
def baseEnd_3359914 : Nat := 1725250839770672554723043

theorem tailTrace_3359914 : CollatzResearch.WordTrace tailWord_3359914 prefixEnd_3359914 1725250839770672554723043 := by
  unfold tailWord_3359914
  simp only [CollatzResearch.WordTrace]
  refine ⟨30636532787403220117889699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81697420766408586981039197 30636532787403220117889699)
  ·
    refine ⟨45954799181104830176834549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30636532787403220117889699 45954799181104830176834549)
    ·
      refine ⟨4308262423228577829078239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45954799181104830176834549 4308262423228577829078239)
      ·
        refine ⟨6462393634842866743617359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308262423228577829078239 6462393634842866743617359)
        ·
          refine ⟨9693590452264300115426039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462393634842866743617359 9693590452264300115426039)
          ·
            refine ⟨14540385678396450173139059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9693590452264300115426039 14540385678396450173139059)
            ·
              refine ⟨21810578517594675259708589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14540385678396450173139059 21810578517594675259708589)
              ·
                refine ⟨8178966944098003222390721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21810578517594675259708589 8178966944098003222390721)
                ·
                  refine ⟨6134225208073502416793041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8178966944098003222390721 6134225208073502416793041)
                  ·
                    refine ⟨4600668906055126812594781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6134225208073502416793041 4600668906055126812594781)
                    ·
                      refine ⟨1725250839770672554723043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4600668906055126812594781 1725250839770672554723043)
                      ·
                        rfl

theorem cell23_3359914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_3359914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359914 prefixEnd_3359914 := by exact prefixLift 3359914
  have htrace : WordTrace (prefixWord ++ tailWord_3359914) baseStart_3359914 baseEnd_3359914 := by
    simpa [prefixWord, tailWord_3359914, baseEnd_3359914] using wordTrace_append hprefix tailTrace_3359914
  have hstable : (prefixWord ++ tailWord_3359914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359914).length < 2 ^ (prefixWord ++ tailWord_3359914).sum := by decide
  have hdescent : baseEnd_3359914 < baseStart_3359914 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3359981 : List Nat := [1, 5, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_3359981 : Nat := 118140960795 + 3359981 * 2 ^ 59
def prefixEnd_3359981 : Nat := 4983230072969 + 3 ^ 40 * 3359981 * 2
def baseEnd_3359981 : Nat := 575095080991507930861745

theorem tailTrace_3359981 : CollatzResearch.WordTrace tailWord_3359981 prefixEnd_3359981 575095080991507930861745 := by
  unfold tailWord_3359981
  simp only [CollatzResearch.WordTrace]
  refine ⟨122548574840370150914247797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81699049893580100609498531 122548574840370150914247797)
  ·
    refine ⟨11488928891284701648210731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122548574840370150914247797 11488928891284701648210731)
    ·
      refine ⟨17233393336927052472316097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11488928891284701648210731 17233393336927052472316097)
      ·
        refine ⟨12925045002695289354237073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17233393336927052472316097 12925045002695289354237073)
        ·
          refine ⟨9693783752021467015677805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12925045002695289354237073 9693783752021467015677805)
          ·
            refine ⟨3635168907008050130879177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9693783752021467015677805 3635168907008050130879177)
            ·
              refine ⟨2726376680256037598159383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635168907008050130879177 2726376680256037598159383)
              ·
                refine ⟨4089565020384056397239075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726376680256037598159383 4089565020384056397239075)
                ·
                  refine ⟨6134347530576084595858613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089565020384056397239075 6134347530576084595858613)
                  ·
                    refine ⟨575095080991507930861745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6134347530576084595858613 575095080991507930861745)
                    ·
                      rfl

theorem cell23_3359981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_3359981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3359981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3359981 prefixEnd_3359981 := by exact prefixLift 3359981
  have htrace : WordTrace (prefixWord ++ tailWord_3359981) baseStart_3359981 baseEnd_3359981 := by
    simpa [prefixWord, tailWord_3359981, baseEnd_3359981] using wordTrace_append hprefix tailTrace_3359981
  have hstable : (prefixWord ++ tailWord_3359981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3359981).length < 2 ^ (prefixWord ++ tailWord_3359981).sum := by decide
  have hdescent : baseEnd_3359981 < baseStart_3359981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3359981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360001 : List Nat := [1, 2, 4, 1, 1, 4, 2, 1, 3, 2, 2]
def baseStart_3360001 : Nat := 118140960795 + 3360001 * 2 ^ 59
def prefixEnd_3360001 : Nat := 4983230072969 + 3 ^ 40 * 3360001 * 2
def baseEnd_3360001 : Nat := 1725295512587613714335143

theorem tailTrace_3360001 : CollatzResearch.WordTrace tailWord_3360001 prefixEnd_3360001 1725295512587613714335143 := by
  unfold tailWord_3360001
  simp only [CollatzResearch.WordTrace]
  refine ⟨122549304300297694329975857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81699536200198462886650571 122549304300297694329975857)
  ·
    refine ⟨91911978225223270747481893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122549304300297694329975857 91911978225223270747481893)
    ·
      refine ⟨17233495917229363265152855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91911978225223270747481893 17233495917229363265152855)
      ·
        refine ⟨25850243875844044897729283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17233495917229363265152855 25850243875844044897729283)
        ·
          refine ⟨38775365813766067346593925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25850243875844044897729283 38775365813766067346593925)
          ·
            refine ⟨7270381090081137627486361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38775365813766067346593925 7270381090081137627486361)
            ·
              refine ⟨5452785817560853220614771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270381090081137627486361 5452785817560853220614771)
              ·
                refine ⟨8179178726341279830922157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452785817560853220614771 8179178726341279830922157)
                ·
                  refine ⟨3067192022377979936595809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8179178726341279830922157 3067192022377979936595809)
                  ·
                    refine ⟨2300394016783484952446857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3067192022377979936595809 2300394016783484952446857)
                    ·
                      refine ⟨1725295512587613714335143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300394016783484952446857 1725295512587613714335143)
                      ·
                        rfl

theorem cell23_3360001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_3360001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360001 prefixEnd_3360001 := by exact prefixLift 3360001
  have htrace : WordTrace (prefixWord ++ tailWord_3360001) baseStart_3360001 baseEnd_3360001 := by
    simpa [prefixWord, tailWord_3360001, baseEnd_3360001] using wordTrace_append hprefix tailTrace_3360001
  have hstable : (prefixWord ++ tailWord_3360001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360001).length < 2 ^ (prefixWord ++ tailWord_3360001).sum := by decide
  have hdescent : baseEnd_3360001 < baseStart_3360001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360014 : List Nat := [4, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3360014 : Nat := 118140960795 + 3360014 * 2 ^ 59
def prefixEnd_3360014 : Nat := 4983230072969 + 3 ^ 40 * 3360014 * 2
def baseEnd_3360014 : Nat := 1725302187836122163472583

theorem tailTrace_3360014 : CollatzResearch.WordTrace tailWord_3360014 prefixEnd_3360014 1725302187836122163472583 := by
  unfold tailWord_3360014
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318722306156324693774887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81699852299500398366799397 15318722306156324693774887)
  ·
    refine ⟨22978083459234487040662331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15318722306156324693774887 22978083459234487040662331)
    ·
      refine ⟨34467125188851730560993497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22978083459234487040662331 34467125188851730560993497)
      ·
        refine ⟨25850343891638797920745123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34467125188851730560993497 25850343891638797920745123)
        ·
          refine ⟨38775515837458196881117685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25850343891638797920745123 38775515837458196881117685)
          ·
            refine ⟨3635204609761705957604783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38775515837458196881117685 3635204609761705957604783)
            ·
              refine ⟨5452806914642558936407175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635204609761705957604783 5452806914642558936407175)
              ·
                refine ⟨8179210371963838404610763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452806914642558936407175 8179210371963838404610763)
                ·
                  refine ⟨12268815557945757606916145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8179210371963838404610763 12268815557945757606916145)
                  ·
                    refine ⟨9201611668459318205187109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12268815557945757606916145 9201611668459318205187109)
                    ·
                      refine ⟨1725302187836122163472583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9201611668459318205187109 1725302187836122163472583)
                      ·
                        rfl

theorem cell23_3360014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3360014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360014 prefixEnd_3360014 := by exact prefixLift 3360014
  have htrace : WordTrace (prefixWord ++ tailWord_3360014) baseStart_3360014 baseEnd_3360014 := by
    simpa [prefixWord, tailWord_3360014, baseEnd_3360014] using wordTrace_append hprefix tailTrace_3360014
  have hstable : (prefixWord ++ tailWord_3360014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360014).length < 2 ^ (prefixWord ++ tailWord_3360014).sum := by decide
  have hdescent : baseEnd_3360014 < baseStart_3360014 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360018 : List Nat := [3, 2, 4, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3360018 : Nat := 118140960795 + 3360018 * 2 ^ 59
def prefixEnd_3360018 : Nat := 4983230072969 + 3 ^ 40 * 3360018 * 2
def baseEnd_3360018 : Nat := 1725304241758740147822565

theorem tailTrace_3360018 : CollatzResearch.WordTrace tailWord_3360018 prefixEnd_3360018 1725304241758740147822565 := by
  unfold tailWord_3360018
  simp only [CollatzResearch.WordTrace]
  refine ⟨30637481085309026558336177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81699949560824070822229805 30637481085309026558336177)
  ·
    refine ⟨22978110813981769918752133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30637481085309026558336177 22978110813981769918752133)
    ·
      refine ⟨4308395777621581859766025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22978110813981769918752133 4308395777621581859766025)
      ·
        refine ⟨3231296833216186394824519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4308395777621581859766025 3231296833216186394824519)
        ·
          refine ⟨4846945249824279592236779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231296833216186394824519 4846945249824279592236779)
          ·
            refine ⟨7270417874736419388355169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4846945249824279592236779 7270417874736419388355169)
            ·
              refine ⟨5452813406052314541266377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270417874736419388355169 5452813406052314541266377)
              ·
                refine ⟨4089610054539235905949783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452813406052314541266377 4089610054539235905949783)
                ·
                  refine ⟨6134415081808853858924675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089610054539235905949783 6134415081808853858924675)
                  ·
                    refine ⟨9201622622713280788387013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6134415081808853858924675 9201622622713280788387013)
                    ·
                      refine ⟨1725304241758740147822565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9201622622713280788387013 1725304241758740147822565)
                      ·
                        rfl

theorem cell23_3360018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3360018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360018 prefixEnd_3360018 := by exact prefixLift 3360018
  have htrace : WordTrace (prefixWord ++ tailWord_3360018) baseStart_3360018 baseEnd_3360018 := by
    simpa [prefixWord, tailWord_3360018, baseEnd_3360018] using wordTrace_append hprefix tailTrace_3360018
  have hstable : (prefixWord ++ tailWord_3360018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360018).length < 2 ^ (prefixWord ++ tailWord_3360018).sum := by decide
  have hdescent : baseEnd_3360018 < baseStart_3360018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360068 : List Nat := [2, 3, 4, 1, 1, 2, 1, 3, 2, 1, 3]
def baseStart_3360068 : Nat := 118140960795 + 3360068 * 2 ^ 59
def prefixEnd_3360068 : Nat := 4983230072969 + 3 ^ 40 * 3360068 * 2
def baseEnd_3360068 : Nat := 1725329915791464952197335

theorem tailTrace_3360068 : CollatzResearch.WordTrace tailWord_3360068 prefixEnd_3360068 1725329915791464952197335 := by
  unfold tailWord_3360068
  simp only [CollatzResearch.WordTrace]
  refine ⟨61275873995527482386332429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81701165327369976515109905 61275873995527482386332429)
  ·
    refine ⟨22978452748322805894874661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61275873995527482386332429 22978452748322805894874661)
    ·
      refine ⟨4308459890310526105288999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22978452748322805894874661 4308459890310526105288999)
      ·
        refine ⟨6462689835465789157933499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308459890310526105288999 6462689835465789157933499)
        ·
          refine ⟨9694034753198683736900249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462689835465789157933499 9694034753198683736900249)
          ·
            refine ⟨7270526064899012802675187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9694034753198683736900249 7270526064899012802675187)
            ·
              refine ⟨10905789097348519204012781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7270526064899012802675187 10905789097348519204012781)
              ·
                refine ⟨4089670911505694701504793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10905789097348519204012781 4089670911505694701504793)
                ·
                  refine ⟨3067253183629271026128595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4089670911505694701504793 3067253183629271026128595)
                  ·
                    refine ⟨4600879775443906539192893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3067253183629271026128595 4600879775443906539192893)
                    ·
                      refine ⟨1725329915791464952197335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4600879775443906539192893 1725329915791464952197335)
                      ·
                        rfl

theorem cell23_3360068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 1, 3, 2, 1, 3].length) (baseStart_3360068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360068 prefixEnd_3360068 := by exact prefixLift 3360068
  have htrace : WordTrace (prefixWord ++ tailWord_3360068) baseStart_3360068 baseEnd_3360068 := by
    simpa [prefixWord, tailWord_3360068, baseEnd_3360068] using wordTrace_append hprefix tailTrace_3360068
  have hstable : (prefixWord ++ tailWord_3360068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360068).length < 2 ^ (prefixWord ++ tailWord_3360068).sum := by decide
  have hdescent : baseEnd_3360068 < baseStart_3360068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360080 : List Nat := [2, 1, 1, 1, 1, 5, 2, 1, 9]
def baseStart_3360080 : Nat := 118140960795 + 3360080 * 2 ^ 59
def prefixEnd_3360080 : Nat := 4983230072969 + 3 ^ 40 * 3360080 * 2
def baseEnd_3360080 : Nat := 191704008617702100583031

theorem tailTrace_3360080 : CollatzResearch.WordTrace tailWord_3360080 prefixEnd_3360080 191704008617702100583031 := by
  unfold tailWord_3360080
  simp only [CollatzResearch.WordTrace]
  refine ⟨61276092833505745411050847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81701457111340993881401129 61276092833505745411050847)
  ·
    refine ⟨91914139250258618116576271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61276092833505745411050847 91914139250258618116576271)
    ·
      refine ⟨137871208875387927174864407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91914139250258618116576271 137871208875387927174864407)
      ·
        refine ⟨206806813313081890762296611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137871208875387927174864407 206806813313081890762296611)
        ·
          refine ⟨310210219969622836143444917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206806813313081890762296611 310210219969622836143444917)
          ·
            refine ⟨29082208122152140888447961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 310210219969622836143444917 29082208122152140888447961)
            ·
              refine ⟨21811656091614105666335971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29082208122152140888447961 21811656091614105666335971)
              ·
                refine ⟨32717484137421158499503957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21811656091614105666335971 32717484137421158499503957)
                ·
                  refine ⟨191704008617702100583031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32717484137421158499503957 191704008617702100583031)
                  ·
                    rfl

theorem cell23_3360080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 1, 9].length) (baseStart_3360080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360080 prefixEnd_3360080 := by exact prefixLift 3360080
  have htrace : WordTrace (prefixWord ++ tailWord_3360080) baseStart_3360080 baseEnd_3360080 := by
    simpa [prefixWord, tailWord_3360080, baseEnd_3360080] using wordTrace_append hprefix tailTrace_3360080
  have hstable : (prefixWord ++ tailWord_3360080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360080).length < 2 ^ (prefixWord ++ tailWord_3360080).sum := by decide
  have hdescent : baseEnd_3360080 < baseStart_3360080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360108 : List Nat := [2, 2, 1, 1, 5, 2, 2, 2, 2, 2, 2]
def baseStart_3360108 : Nat := 118140960795 + 3360108 * 2 ^ 59
def prefixEnd_3360108 : Nat := 4983230072969 + 3 ^ 40 * 3360108 * 2
def baseEnd_3360108 : Nat := 1725350455017644795697151

theorem tailTrace_3360108 : CollatzResearch.WordTrace tailWord_3360108 prefixEnd_3360108 1725350455017644795697151 := by
  unfold tailWord_3360108
  simp only [CollatzResearch.WordTrace]
  refine ⟨61276603455455025802060489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81702137940606701069413985 61276603455455025802060489)
  ·
    refine ⟨45957452591591269351545367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61276603455455025802060489 45957452591591269351545367)
    ·
      refine ⟨68936178887386904027318051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45957452591591269351545367 68936178887386904027318051)
      ·
        refine ⟨103404268331080356040977077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68936178887386904027318051 103404268331080356040977077)
        ·
          refine ⟨9694150156038783378841601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103404268331080356040977077 9694150156038783378841601)
          ·
            refine ⟨7270612617029087534131201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9694150156038783378841601 7270612617029087534131201)
            ·
              refine ⟨5452959462771815650598401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7270612617029087534131201 5452959462771815650598401)
              ·
                refine ⟨4089719597078861737948801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452959462771815650598401 4089719597078861737948801)
                ·
                  refine ⟨3067289697809146303461601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4089719597078861737948801 3067289697809146303461601)
                  ·
                    refine ⟨2300467273356859727596201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3067289697809146303461601 2300467273356859727596201)
                    ·
                      refine ⟨1725350455017644795697151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300467273356859727596201 1725350455017644795697151)
                      ·
                        rfl

theorem cell23_3360108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_3360108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360108 prefixEnd_3360108 := by exact prefixLift 3360108
  have htrace : WordTrace (prefixWord ++ tailWord_3360108) baseStart_3360108 baseEnd_3360108 := by
    simpa [prefixWord, tailWord_3360108, baseEnd_3360108] using wordTrace_append hprefix tailTrace_3360108
  have hstable : (prefixWord ++ tailWord_3360108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360108).length < 2 ^ (prefixWord ++ tailWord_3360108).sum := by decide
  have hdescent : baseEnd_3360108 < baseStart_3360108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360114 : List Nat := [3, 2, 1, 2, 1, 2, 3, 4, 5]
def baseStart_3360114 : Nat := 118140960795 + 3360114 * 2 ^ 59
def prefixEnd_3360114 : Nat := 4983230072969 + 3 ^ 40 * 3360114 * 2
def baseEnd_3360114 : Nat := 191705948433507974691347

theorem tailTrace_3360114 : CollatzResearch.WordTrace tailWord_3360114 prefixEnd_3360114 191705948433507974691347 := by
  unfold tailWord_3360114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30638356437222078657209849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81702283832592209752559597 30638356437222078657209849)
  ·
    refine ⟨22978767327916558992907387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30638356437222078657209849 22978767327916558992907387)
    ·
      refine ⟨34468150991874838489361081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22978767327916558992907387 34468150991874838489361081)
      ·
        refine ⟨25851113243906128867020811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34468150991874838489361081 25851113243906128867020811)
        ·
          refine ⟨38776669865859193300531217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25851113243906128867020811 38776669865859193300531217)
          ·
            refine ⟨29082502399394394975398413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38776669865859193300531217 29082502399394394975398413)
            ·
              refine ⟨10905938399772898115774405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29082502399394394975398413 10905938399772898115774405)
              ·
                refine ⟨2044863449957418396707701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10905938399772898115774405 2044863449957418396707701)
                ·
                  refine ⟨191705948433507974691347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2044863449957418396707701 191705948433507974691347)
                  ·
                    rfl

theorem cell23_3360114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_3360114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360114 prefixEnd_3360114 := by exact prefixLift 3360114
  have htrace : WordTrace (prefixWord ++ tailWord_3360114) baseStart_3360114 baseEnd_3360114 := by
    simpa [prefixWord, tailWord_3360114, baseEnd_3360114] using wordTrace_append hprefix tailTrace_3360114
  have hstable : (prefixWord ++ tailWord_3360114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360114).length < 2 ^ (prefixWord ++ tailWord_3360114).sum := by decide
  have hdescent : baseEnd_3360114 < baseStart_3360114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360177 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_3360177 : Nat := 118140960795 + 3360177 * 2 ^ 59
def prefixEnd_3360177 : Nat := 4983230072969 + 3 ^ 40 * 3360177 * 2
def baseEnd_3360177 : Nat := 1725385885182805025734333

theorem tailTrace_3360177 : CollatzResearch.WordTrace tailWord_3360177 prefixEnd_3360177 1725385885182805025734333 := by
  unfold tailWord_3360177
  simp only [CollatzResearch.WordTrace]
  refine ⟨122555723547660076388382785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81703815698440050925588523 122555723547660076388382785)
  ·
    refine ⟨91916792660745057291287089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122555723547660076388382785 91916792660745057291287089)
    ·
      refine ⟨68937594495558792968465317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91916792660745057291287089 68937594495558792968465317)
      ·
        refine ⟨12925798967917273681587247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68937594495558792968465317 12925798967917273681587247)
        ·
          refine ⟨19388698451875910522380871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12925798967917273681587247 19388698451875910522380871)
          ·
            refine ⟨29083047677813865783571307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19388698451875910522380871 29083047677813865783571307)
            ·
              refine ⟨43624571516720798675356961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29083047677813865783571307 43624571516720798675356961)
              ·
                refine ⟨32718428637540599006517721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43624571516720798675356961 32718428637540599006517721)
                ·
                  refine ⟨24538821478155449254888291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32718428637540599006517721 24538821478155449254888291)
                  ·
                    refine ⟨36808232217233173882332437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24538821478155449254888291 36808232217233173882332437)
                    ·
                      refine ⟨1725385885182805025734333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36808232217233173882332437 1725385885182805025734333)
                      ·
                        rfl

theorem cell23_3360177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_3360177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360177 prefixEnd_3360177 := by exact prefixLift 3360177
  have htrace : WordTrace (prefixWord ++ tailWord_3360177) baseStart_3360177 baseEnd_3360177 := by
    simpa [prefixWord, tailWord_3360177, baseEnd_3360177] using wordTrace_append hprefix tailTrace_3360177
  have hstable : (prefixWord ++ tailWord_3360177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360177).length < 2 ^ (prefixWord ++ tailWord_3360177).sum := by decide
  have hdescent : baseEnd_3360177 < baseStart_3360177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360181 : List Nat := [1, 3, 3, 2, 2, 1, 2, 1, 2, 4, 2]
def baseStart_3360181 : Nat := 118140960795 + 3360181 * 2 ^ 59
def prefixEnd_3360181 : Nat := 4983230072969 + 3 ^ 40 * 3360181 * 2
def baseEnd_3360181 : Nat := 1725387939105423010084315

theorem tailTrace_3360181 : CollatzResearch.WordTrace tailWord_3360181 prefixEnd_3360181 1725387939105423010084315 := by
  unfold tailWord_3360181
  simp only [CollatzResearch.WordTrace]
  refine ⟨122555869439645585071528397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81703912959763723381018931 122555869439645585071528397)
  ·
    refine ⟨45958451039867094401823149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122555869439645585071528397 45958451039867094401823149)
    ·
      refine ⟨17234419139950160400683681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45958451039867094401823149 17234419139950160400683681)
      ·
        refine ⟨12925814354962620300512761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17234419139950160400683681 12925814354962620300512761)
        ·
          refine ⟨9694360766221965225384571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12925814354962620300512761 9694360766221965225384571)
          ·
            refine ⟨14541541149332947838076857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9694360766221965225384571 14541541149332947838076857)
            ·
              refine ⟨10906155861999710878557643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14541541149332947838076857 10906155861999710878557643)
              ·
                refine ⟨16359233792999566317836465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906155861999710878557643 16359233792999566317836465)
                ·
                  refine ⟨12269425344749674738377349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16359233792999566317836465 12269425344749674738377349)
                  ·
                    refine ⟨2300517252140564013445753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12269425344749674738377349 2300517252140564013445753)
                    ·
                      refine ⟨1725387939105423010084315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300517252140564013445753 1725387939105423010084315)
                      ·
                        rfl

theorem cell23_3360181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_3360181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360181 prefixEnd_3360181 := by exact prefixLift 3360181
  have htrace : WordTrace (prefixWord ++ tailWord_3360181) baseStart_3360181 baseEnd_3360181 := by
    simpa [prefixWord, tailWord_3360181, baseEnd_3360181] using wordTrace_append hprefix tailTrace_3360181
  have hstable : (prefixWord ++ tailWord_3360181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360181).length < 2 ^ (prefixWord ++ tailWord_3360181).sum := by decide
  have hdescent : baseEnd_3360181 < baseStart_3360181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360224 : List Nat := [2, 1, 1, 3, 1, 1, 2, 2, 3, 5, 2]
def baseStart_3360224 : Nat := 118140960795 + 3360224 * 2 ^ 59
def prefixEnd_3360224 : Nat := 4983230072969 + 3 ^ 40 * 3360224 * 2
def baseEnd_3360224 : Nat := 1725410018773566341846617

theorem tailTrace_3360224 : CollatzResearch.WordTrace tailWord_3360224 prefixEnd_3360224 1725410018773566341846617 := by
  unfold tailWord_3360224
  simp only [CollatzResearch.WordTrace]
  refine ⟨61278718889244901707671863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81704958518993202276895817 61278718889244901707671863)
  ·
    refine ⟨91918078333867352561507795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61278718889244901707671863 91918078333867352561507795)
    ·
      refine ⟨137877117500801028842261693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91918078333867352561507795 137877117500801028842261693)
      ·
        refine ⟨51703919062800385815848135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137877117500801028842261693 51703919062800385815848135)
        ·
          refine ⟨77555878594200578723772203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51703919062800385815848135 77555878594200578723772203)
          ·
            refine ⟨116333817891300868085658305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77555878594200578723772203 116333817891300868085658305)
            ·
              refine ⟨87250363418475651064243729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116333817891300868085658305 87250363418475651064243729)
              ·
                refine ⟨65437772563856738298182797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87250363418475651064243729 65437772563856738298182797)
                ·
                  refine ⟨24539164711446276861818549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65437772563856738298182797 24539164711446276861818549)
                  ·
                    refine ⟨2300546691698088455795489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24539164711446276861818549 2300546691698088455795489)
                    ·
                      refine ⟨1725410018773566341846617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300546691698088455795489 1725410018773566341846617)
                      ·
                        rfl

theorem cell23_3360224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 2, 3, 5, 2].length) (baseStart_3360224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360224 prefixEnd_3360224 := by exact prefixLift 3360224
  have htrace : WordTrace (prefixWord ++ tailWord_3360224) baseStart_3360224 baseEnd_3360224 := by
    simpa [prefixWord, tailWord_3360224, baseEnd_3360224] using wordTrace_append hprefix tailTrace_3360224
  have hstable : (prefixWord ++ tailWord_3360224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360224).length < 2 ^ (prefixWord ++ tailWord_3360224).sum := by decide
  have hdescent : baseEnd_3360224 < baseStart_3360224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360264 : List Nat := [2, 1, 3, 2, 1, 1, 2, 1, 6, 4]
def baseStart_3360264 : Nat := 118140960795 + 3360264 * 2 ^ 59
def prefixEnd_3360264 : Nat := 4983230072969 + 3 ^ 40 * 3360264 * 2
def baseEnd_3360264 : Nat := 575143519333248728448811

theorem tailTrace_3360264 : CollatzResearch.WordTrace tailWord_3360264 prefixEnd_3360264 575143519333248728448811 := by
  unfold tailWord_3360264
  simp only [CollatzResearch.WordTrace]
  refine ⟨61279448349172445123399923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81705931132229926831199897 61279448349172445123399923)
  ·
    refine ⟨91919172523758667685099885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61279448349172445123399923 91919172523758667685099885)
    ·
      refine ⟨34469689696409500381912457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91919172523758667685099885 34469689696409500381912457)
      ·
        refine ⟨25852267272307125286434343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34469689696409500381912457 25852267272307125286434343)
        ·
          refine ⟨38778400908460687929651515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25852267272307125286434343 38778400908460687929651515)
          ·
            refine ⟨58167601362691031894477273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38778400908460687929651515 58167601362691031894477273)
            ·
              refine ⟨43625701022018273920857955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58167601362691031894477273 43625701022018273920857955)
              ·
                refine ⟨65438551533027410881286933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43625701022018273920857955 65438551533027410881286933)
                ·
                  refine ⟨3067432103110659885060325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65438551533027410881286933 3067432103110659885060325)
                  ·
                    refine ⟨575143519333248728448811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3067432103110659885060325 575143519333248728448811)
                    ·
                      rfl

theorem cell23_3360264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_3360264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360264 prefixEnd_3360264 := by exact prefixLift 3360264
  have htrace : WordTrace (prefixWord ++ tailWord_3360264) baseStart_3360264 baseEnd_3360264 := by
    simpa [prefixWord, tailWord_3360264, baseEnd_3360264] using wordTrace_append hprefix tailTrace_3360264
  have hstable : (prefixWord ++ tailWord_3360264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360264).length < 2 ^ (prefixWord ++ tailWord_3360264).sum := by decide
  have hdescent : baseEnd_3360264 < baseStart_3360264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360268 : List Nat := [2, 2, 1, 2, 5, 1, 3, 1, 1, 5]
def baseStart_3360268 : Nat := 118140960795 + 3360268 * 2 ^ 59
def prefixEnd_3360268 : Nat := 4983230072969 + 3 ^ 40 * 3360268 * 2
def baseEnd_3360268 : Nat := 575144203974121389898805

theorem tailTrace_3360268 : CollatzResearch.WordTrace tailWord_3360268 prefixEnd_3360268 575144203974121389898805 := by
  unfold tailWord_3360268
  simp only [CollatzResearch.WordTrace]
  refine ⟨61279521295165199464972729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81706028393553599286630305 61279521295165199464972729)
  ·
    refine ⟨45959640971373899598729547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61279521295165199464972729 45959640971373899598729547)
    ·
      refine ⟨68939461457060849398094321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45959640971373899598729547 68939461457060849398094321)
      ·
        refine ⟨51704596092795637048570741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68939461457060849398094321 51704596092795637048570741)
        ·
          refine ⟨4847305883699590973303507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51704596092795637048570741 4847305883699590973303507)
          ·
            refine ⟨7270958825549386459955261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847305883699590973303507 7270958825549386459955261)
            ·
              refine ⟨2726609559581019922483223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7270958825549386459955261 2726609559581019922483223)
              ·
                refine ⟨4089914339371529883724835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726609559581019922483223 4089914339371529883724835)
                ·
                  refine ⟨6134871509057294825587253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4089914339371529883724835 6134871509057294825587253)
                  ·
                    refine ⟨575144203974121389898805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6134871509057294825587253 575144203974121389898805)
                    ·
                      rfl

theorem cell23_3360268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_3360268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360268 prefixEnd_3360268 := by exact prefixLift 3360268
  have htrace : WordTrace (prefixWord ++ tailWord_3360268) baseStart_3360268 baseEnd_3360268 := by
    simpa [prefixWord, tailWord_3360268, baseEnd_3360268] using wordTrace_append hprefix tailTrace_3360268
  have hstable : (prefixWord ++ tailWord_3360268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360268).length < 2 ^ (prefixWord ++ tailWord_3360268).sum := by decide
  have hdescent : baseEnd_3360268 < baseStart_3360268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360277 : List Nat := [1, 3, 2, 1, 3, 13]
def baseStart_3360277 : Nat := 118140960795 + 3360277 * 2 ^ 59
def prefixEnd_3360277 : Nat := 4983230072969 + 3 ^ 40 * 3360277 * 2
def baseEnd_3360277 : Nat := 7100564745877591088411

theorem tailTrace_3360277 : CollatzResearch.WordTrace tailWord_3360277 prefixEnd_3360277 7100564745877591088411 := by
  unfold tailWord_3360277
  simp only [CollatzResearch.WordTrace]
  refine ⟨122559370847297793467023085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81706247231531862311348723 122559370847297793467023085)
  ·
    refine ⟨45959764067736672550133657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122559370847297793467023085 45959764067736672550133657)
    ·
      refine ⟨34469823050802504412600243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45959764067736672550133657 34469823050802504412600243)
      ·
        refine ⟨51704734576203756618900365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34469823050802504412600243 51704734576203756618900365)
        ·
          refine ⟨19389275466076408732087637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51704734576203756618900365 19389275466076408732087637)
          ·
            refine ⟨7100564745877591088411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 19389275466076408732087637 7100564745877591088411)
            ·
              rfl

theorem cell23_3360277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 13].length) (baseStart_3360277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360277 prefixEnd_3360277 := by exact prefixLift 3360277
  have htrace : WordTrace (prefixWord ++ tailWord_3360277) baseStart_3360277 baseEnd_3360277 := by
    simpa [prefixWord, tailWord_3360277, baseEnd_3360277] using wordTrace_append hprefix tailTrace_3360277
  have hstable : (prefixWord ++ tailWord_3360277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360277).length < 2 ^ (prefixWord ++ tailWord_3360277).sum := by decide
  have hdescent : baseEnd_3360277 < baseStart_3360277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360284 : List Nat := [2, 2, 3, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_3360284 : Nat := 118140960795 + 3360284 * 2 ^ 59
def prefixEnd_3360284 : Nat := 4983230072969 + 3 ^ 40 * 3360284 * 2
def baseEnd_3360284 : Nat := 1725440827612836107096341

theorem tailTrace_3360284 : CollatzResearch.WordTrace tailWord_3360284 prefixEnd_3360284 1725440827612836107096341 := by
  unfold tailWord_3360284
  simp only [CollatzResearch.WordTrace]
  refine ⟨61279813079136216831263953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81706417438848289108351937 61279813079136216831263953)
  ·
    refine ⟨45959859809352162623447965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61279813079136216831263953 45959859809352162623447965)
    ·
      refine ⟨17234947428507060983792987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45959859809352162623447965 17234947428507060983792987)
      ·
        refine ⟨25852421142760591475689481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17234947428507060983792987 25852421142760591475689481)
        ·
          refine ⟨19389315857070443606767111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25852421142760591475689481 19389315857070443606767111)
          ·
            refine ⟨29083973785605665410150667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19389315857070443606767111 29083973785605665410150667)
            ·
              refine ⟨43625960678408498115226001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29083973785605665410150667 43625960678408498115226001)
              ·
                refine ⟨32719470508806373586419501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43625960678408498115226001 32719470508806373586419501)
                ·
                  refine ⟨12269801440802390094907313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32719470508806373586419501 12269801440802390094907313)
                  ·
                    refine ⟨9202351080601792571180485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12269801440802390094907313 9202351080601792571180485)
                    ·
                      refine ⟨1725440827612836107096341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9202351080601792571180485 1725440827612836107096341)
                      ·
                        rfl

theorem cell23_3360284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_3360284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360284 prefixEnd_3360284 := by exact prefixLift 3360284
  have htrace : WordTrace (prefixWord ++ tailWord_3360284) baseStart_3360284 baseEnd_3360284 := by
    simpa [prefixWord, tailWord_3360284, baseEnd_3360284] using wordTrace_append hprefix tailTrace_3360284
  have hstable : (prefixWord ++ tailWord_3360284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360284).length < 2 ^ (prefixWord ++ tailWord_3360284).sum := by decide
  have hdescent : baseEnd_3360284 < baseStart_3360284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360321 : List Nat := [1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 3]
def baseStart_3360321 : Nat := 118140960795 + 3360321 * 2 ^ 59
def prefixEnd_3360321 : Nat := 4983230072969 + 3 ^ 40 * 3360321 * 2
def baseEnd_3360321 : Nat := 1725459826397052462333671

theorem tailTrace_3360321 : CollatzResearch.WordTrace tailWord_3360321 prefixEnd_3360321 1725459826397052462333671 := by
  unfold tailWord_3360321
  simp only [CollatzResearch.WordTrace]
  refine ⟨122560975659138388981624817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81707317106092259321083211 122560975659138388981624817)
  ·
    refine ⟨91920731744353791736218613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122560975659138388981624817 91920731744353791736218613)
    ·
      refine ⟨8617568601033167975270495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91920731744353791736218613 8617568601033167975270495)
      ·
        refine ⟨12926352901549751962905743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8617568601033167975270495 12926352901549751962905743)
        ·
          refine ⟨19389529352324627944358615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12926352901549751962905743 19389529352324627944358615)
          ·
            refine ⟨29084294028486941916537923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19389529352324627944358615 29084294028486941916537923)
            ·
              refine ⟨43626441042730412874806885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29084294028486941916537923 43626441042730412874806885)
              ·
                refine ⟨8179957695511952414026291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43626441042730412874806885 8179957695511952414026291)
                ·
                  refine ⟨12269936543267928621039437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8179957695511952414026291 12269936543267928621039437)
                  ·
                    refine ⟨4601226203725473232889789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12269936543267928621039437 4601226203725473232889789)
                    ·
                      refine ⟨1725459826397052462333671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4601226203725473232889789 1725459826397052462333671)
                      ·
                        rfl

theorem cell23_3360321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_3360321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360321 prefixEnd_3360321 := by exact prefixLift 3360321
  have htrace : WordTrace (prefixWord ++ tailWord_3360321) baseStart_3360321 baseEnd_3360321 := by
    simpa [prefixWord, tailWord_3360321, baseEnd_3360321] using wordTrace_append hprefix tailTrace_3360321
  have hstable : (prefixWord ++ tailWord_3360321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360321).length < 2 ^ (prefixWord ++ tailWord_3360321).sum := by decide
  have hdescent : baseEnd_3360321 < baseStart_3360321 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360338 : List Nat := [3, 2, 2, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_3360338 : Nat := 118140960795 + 3360338 * 2 ^ 59
def prefixEnd_3360338 : Nat := 4983230072969 + 3 ^ 40 * 3360338 * 2
def baseEnd_3360338 : Nat := 1725468555568178895821093

theorem tailTrace_3360338 : CollatzResearch.WordTrace tailWord_3360338 prefixEnd_3360338 1725468555568178895821093 := by
  unfold tailWord_3360338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30640398925019200221248417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81707730466717867256662445 30640398925019200221248417)
  ·
    refine ⟨22980299193764400165936313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30640398925019200221248417 22980299193764400165936313)
    ·
      refine ⟨17235224395323300124452235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22980299193764400165936313 17235224395323300124452235)
      ·
        refine ⟨25852836592984950186678353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17235224395323300124452235 25852836592984950186678353)
        ·
          refine ⟨19389627444738712640008765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25852836592984950186678353 19389627444738712640008765)
          ·
            refine ⟨7271110291777017240003287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19389627444738712640008765 7271110291777017240003287)
            ·
              refine ⟨10906665437665525860004931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271110291777017240003287 10906665437665525860004931)
              ·
                refine ⟨16359998156498288790007397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906665437665525860004931 16359998156498288790007397)
                ·
                  refine ⟨3067499654343429148126387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16359998156498288790007397 3067499654343429148126387)
                  ·
                    refine ⟨4601249481515143722189581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3067499654343429148126387 4601249481515143722189581)
                    ·
                      refine ⟨1725468555568178895821093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4601249481515143722189581 1725468555568178895821093)
                      ·
                        rfl

theorem cell23_3360338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_3360338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360338 prefixEnd_3360338 := by exact prefixLift 3360338
  have htrace : WordTrace (prefixWord ++ tailWord_3360338) baseStart_3360338 baseEnd_3360338 := by
    simpa [prefixWord, tailWord_3360338, baseEnd_3360338] using wordTrace_append hprefix tailTrace_3360338
  have hstable : (prefixWord ++ tailWord_3360338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360338).length < 2 ^ (prefixWord ++ tailWord_3360338).sum := by decide
  have hdescent : baseEnd_3360338 < baseStart_3360338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360355 : List Nat := [1, 1, 1, 5, 1, 4, 3, 1, 2, 1, 3]
def baseStart_3360355 : Nat := 118140960795 + 3360355 * 2 ^ 59
def prefixEnd_3360355 : Nat := 4983230072969 + 3 ^ 40 * 3360355 * 2
def baseEnd_3360355 : Nat := 1725477284739305329308515

theorem tailTrace_3360355 : CollatzResearch.WordTrace tailWord_3360355 prefixEnd_3360355 1725477284739305329308515 := by
  unfold tailWord_3360355
  simp only [CollatzResearch.WordTrace]
  refine ⟨122562215741015212788362519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81708143827343475192241679 122562215741015212788362519)
  ·
    refine ⟨183843323611522819182543779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122562215741015212788362519 183843323611522819182543779)
    ·
      refine ⟨275764985417284228773815669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183843323611522819182543779 275764985417284228773815669)
      ·
        refine ⟨25852967382870396447545219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 275764985417284228773815669 25852967382870396447545219)
        ·
          refine ⟨38779451074305594671317829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25852967382870396447545219 38779451074305594671317829)
          ·
            refine ⟨7271147076432299000872093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38779451074305594671317829 7271147076432299000872093)
            ·
              refine ⟨2726680153662112125327035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7271147076432299000872093 2726680153662112125327035)
              ·
                refine ⟨4090020230493168187990553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726680153662112125327035 4090020230493168187990553)
                ·
                  refine ⟨3067515172869876140992915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4090020230493168187990553 3067515172869876140992915)
                  ·
                    refine ⟨4601272759304814211489373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3067515172869876140992915 4601272759304814211489373)
                    ·
                      refine ⟨1725477284739305329308515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4601272759304814211489373 1725477284739305329308515)
                      ·
                        rfl

theorem cell23_3360355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 3, 1, 2, 1, 3].length) (baseStart_3360355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360355 prefixEnd_3360355 := by exact prefixLift 3360355
  have htrace : WordTrace (prefixWord ++ tailWord_3360355) baseStart_3360355 baseEnd_3360355 := by
    simpa [prefixWord, tailWord_3360355, baseEnd_3360355] using wordTrace_append hprefix tailTrace_3360355
  have hstable : (prefixWord ++ tailWord_3360355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360355).length < 2 ^ (prefixWord ++ tailWord_3360355).sum := by decide
  have hdescent : baseEnd_3360355 < baseStart_3360355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360364 : List Nat := [2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_3360364 : Nat := 118140960795 + 3360364 * 2 ^ 59
def prefixEnd_3360364 : Nat := 4983230072969 + 3 ^ 40 * 3360364 * 2
def baseEnd_3360364 : Nat := 1725481906065195794095973

theorem tailTrace_3360364 : CollatzResearch.WordTrace tailWord_3360364 prefixEnd_3360364 1725481906065195794095973 := by
  unfold tailWord_3360364
  simp only [CollatzResearch.WordTrace]
  refine ⟨61281271998991303662720073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81708362665321738216960097 61281271998991303662720073)
  ·
    refine ⟨45960953999243477747040055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61281271998991303662720073 45960953999243477747040055)
    ·
      refine ⟨68941430998865216620560083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45960953999243477747040055 68941430998865216620560083)
      ·
        refine ⟨103412146498297824930840125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68941430998865216620560083 103412146498297824930840125)
        ·
          refine ⟨38779554936861684349065047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103412146498297824930840125 38779554936861684349065047)
          ·
            refine ⟨58169332405292526523597571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38779554936861684349065047 58169332405292526523597571)
            ·
              refine ⟨87253998607938789785396357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58169332405292526523597571 87253998607938789785396357)
              ·
                refine ⟨16360124738988523084761817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87253998607938789785396357 16360124738988523084761817)
                ·
                  refine ⟨12270093554241392313571363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16360124738988523084761817 12270093554241392313571363)
                  ·
                    refine ⟨18405140331362088470357045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12270093554241392313571363 18405140331362088470357045)
                    ·
                      refine ⟨1725481906065195794095973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18405140331362088470357045 1725481906065195794095973)
                      ·
                        rfl

theorem cell23_3360364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_3360364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360364 prefixEnd_3360364 := by exact prefixLift 3360364
  have htrace : WordTrace (prefixWord ++ tailWord_3360364) baseStart_3360364 baseEnd_3360364 := by
    simpa [prefixWord, tailWord_3360364, baseEnd_3360364] using wordTrace_append hprefix tailTrace_3360364
  have hstable : (prefixWord ++ tailWord_3360364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360364).length < 2 ^ (prefixWord ++ tailWord_3360364).sum := by decide
  have hdescent : baseEnd_3360364 < baseStart_3360364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360381 : List Nat := [1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_3360381 : Nat := 118140960795 + 3360381 * 2 ^ 59
def prefixEnd_3360381 : Nat := 4983230072969 + 3 ^ 40 * 3360381 * 2
def baseEnd_3360381 : Nat := 1725490635236322227583395

theorem tailTrace_3360381 : CollatzResearch.WordTrace tailWord_3360381 prefixEnd_3360381 1725490635236322227583395 := by
  unfold tailWord_3360381
  simp only [CollatzResearch.WordTrace]
  refine ⟨122563164038921019228808997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81708776025947346152539331 122563164038921019228808997)
  ·
    refine ⟨22980593257297691105401687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122563164038921019228808997 22980593257297691105401687)
    ·
      refine ⟨34470889885946536658102531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22980593257297691105401687 34470889885946536658102531)
      ·
        refine ⟨51706334828919804987153797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34470889885946536658102531 51706334828919804987153797)
        ·
          refine ⟨9694937780422463435091337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51706334828919804987153797 9694937780422463435091337)
          ·
            refine ⟨7271203335316847576318503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9694937780422463435091337 7271203335316847576318503)
            ·
              refine ⟨10906805002975271364477755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271203335316847576318503 10906805002975271364477755)
              ·
                refine ⟨16360207504462907046716633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10906805002975271364477755 16360207504462907046716633)
                ·
                  refine ⟨12270155628347180285037475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16360207504462907046716633 12270155628347180285037475)
                  ·
                    refine ⟨18405233442520770427556213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12270155628347180285037475 18405233442520770427556213)
                    ·
                      refine ⟨1725490635236322227583395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18405233442520770427556213 1725490635236322227583395)
                      ·
                        rfl

theorem cell23_3360381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_3360381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360381 prefixEnd_3360381 := by exact prefixLift 3360381
  have htrace : WordTrace (prefixWord ++ tailWord_3360381) baseStart_3360381 baseEnd_3360381 := by
    simpa [prefixWord, tailWord_3360381, baseEnd_3360381] using wordTrace_append hprefix tailTrace_3360381
  have hstable : (prefixWord ++ tailWord_3360381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360381).length < 2 ^ (prefixWord ++ tailWord_3360381).sum := by decide
  have hdescent : baseEnd_3360381 < baseStart_3360381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360412 : List Nat := [2, 2, 3, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_3360412 : Nat := 118140960795 + 3360412 * 2 ^ 59
def prefixEnd_3360412 : Nat := 4983230072969 + 3 ^ 40 * 3360412 * 2
def baseEnd_3360412 : Nat := 1725506553136611606295753

theorem tailTrace_3360412 : CollatzResearch.WordTrace tailWord_3360412 prefixEnd_3360412 1725506553136611606295753 := by
  unfold tailWord_3360412
  simp only [CollatzResearch.WordTrace]
  refine ⟨61282147350904355761593745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81709529801205807682124993 61282147350904355761593745)
  ·
    refine ⟨45961610513178266821195309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61282147350904355761593745 45961610513178266821195309)
    ·
      refine ⟨17235603942441850057948241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45961610513178266821195309 17235603942441850057948241)
      ·
        refine ⟨12926702956831387543461181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17235603942441850057948241 12926702956831387543461181)
        ·
          refine ⟨4847513608811770328797943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12926702956831387543461181 4847513608811770328797943)
          ·
            refine ⟨7271270413217655493196915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847513608811770328797943 7271270413217655493196915)
            ·
              refine ⟨10906905619826483239795373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271270413217655493196915 10906905619826483239795373)
              ·
                refine ⟨4090089607434931214923265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10906905619826483239795373 4090089607434931214923265)
                ·
                  refine ⟨3067567205576198411192449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4090089607434931214923265 3067567205576198411192449)
                  ·
                    refine ⟨2300675404182148808394337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3067567205576198411192449 2300675404182148808394337)
                    ·
                      refine ⟨1725506553136611606295753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300675404182148808394337 1725506553136611606295753)
                      ·
                        rfl

theorem cell23_3360412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_3360412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360412 prefixEnd_3360412 := by exact prefixLift 3360412
  have htrace : WordTrace (prefixWord ++ tailWord_3360412) baseStart_3360412 baseEnd_3360412 := by
    simpa [prefixWord, tailWord_3360412, baseEnd_3360412] using wordTrace_append hprefix tailTrace_3360412
  have hstable : (prefixWord ++ tailWord_3360412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360412).length < 2 ^ (prefixWord ++ tailWord_3360412).sum := by decide
  have hdescent : baseEnd_3360412 < baseStart_3360412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360431 : List Nat := [1, 1, 2, 1, 2, 4, 4, 1, 2, 5]
def baseStart_3360431 : Nat := 118140960795 + 3360431 * 2 ^ 59
def prefixEnd_3360431 : Nat := 4983230072969 + 3 ^ 40 * 3360431 * 2
def baseEnd_3360431 : Nat := 575172103089682343986055

theorem tailTrace_3360431 : CollatzResearch.WordTrace tailWord_3360431 prefixEnd_3360431 575172103089682343986055 := by
  unfold tailWord_3360431
  simp only [CollatzResearch.WordTrace]
  refine ⟨122564987688739877768129147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81709991792493251845419431 122564987688739877768129147)
  ·
    refine ⟨183847481533109816652193721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122564987688739877768129147 183847481533109816652193721)
    ·
      refine ⟨137885611149832362489145291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183847481533109816652193721 137885611149832362489145291)
      ·
        refine ⟨206828416724748543733717937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137885611149832362489145291 206828416724748543733717937)
        ·
          refine ⟨155121312543561407800288453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206828416724748543733717937 155121312543561407800288453)
          ·
            refine ⟨29085246101917763962554085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155121312543561407800288453 29085246101917763962554085)
            ·
              refine ⟨5453483644109580742978891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29085246101917763962554085 5453483644109580742978891)
              ·
                refine ⟨8180225466164371114468337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453483644109580742978891 8180225466164371114468337)
                ·
                  refine ⟨6135169099623278335851253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8180225466164371114468337 6135169099623278335851253)
                  ·
                    refine ⟨575172103089682343986055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6135169099623278335851253 575172103089682343986055)
                    ·
                      rfl

theorem cell23_3360431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 4, 1, 2, 5].length) (baseStart_3360431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360431 prefixEnd_3360431 := by exact prefixLift 3360431
  have htrace : WordTrace (prefixWord ++ tailWord_3360431) baseStart_3360431 baseEnd_3360431 := by
    simpa [prefixWord, tailWord_3360431, baseEnd_3360431] using wordTrace_append hprefix tailTrace_3360431
  have hstable : (prefixWord ++ tailWord_3360431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360431).length < 2 ^ (prefixWord ++ tailWord_3360431).sum := by decide
  have hdescent : baseEnd_3360431 < baseStart_3360431 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360451 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 5, 6, 2]
def baseStart_3360451 : Nat := 118140960795 + 3360451 * 2 ^ 59
def prefixEnd_3360451 : Nat := 4983230072969 + 3 ^ 40 * 3360451 * 2
def baseEnd_3360451 : Nat := 1725526578882136953708073

theorem tailTrace_3360451 : CollatzResearch.WordTrace tailWord_3360451 prefixEnd_3360451 1725526578882136953708073 := by
  unfold tailWord_3360451
  simp only [CollatzResearch.WordTrace]
  refine ⟨122565717148667421183857207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81710478099111614122571471 122565717148667421183857207)
  ·
    refine ⟨183848575723001131775785811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122565717148667421183857207 183848575723001131775785811)
    ·
      refine ⟨275772863584501697663678717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183848575723001131775785811 275772863584501697663678717)
      ·
        refine ⟨103414823844188136623879519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 275772863584501697663678717 103414823844188136623879519)
        ·
          refine ⟨155122235766282204935819279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103414823844188136623879519 155122235766282204935819279)
          ·
            refine ⟨232683353649423307403728919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155122235766282204935819279 232683353649423307403728919)
            ·
              refine ⟨349025030474134961105593379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232683353649423307403728919 349025030474134961105593379)
              ·
                refine ⟨523537545711202441658390069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 349025030474134961105593379 523537545711202441658390069)
                ·
                  refine ⟨49081644910425228905474069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 523537545711202441658390069 49081644910425228905474069)
                  ·
                    refine ⟨2300702105176182604944097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49081644910425228905474069 2300702105176182604944097)
                    ·
                      refine ⟨1725526578882136953708073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300702105176182604944097 1725526578882136953708073)
                      ·
                        rfl

theorem cell23_3360451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 6, 2].length) (baseStart_3360451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360451 prefixEnd_3360451 := by exact prefixLift 3360451
  have htrace : WordTrace (prefixWord ++ tailWord_3360451) baseStart_3360451 baseEnd_3360451 := by
    simpa [prefixWord, tailWord_3360451, baseEnd_3360451] using wordTrace_append hprefix tailTrace_3360451
  have hstable : (prefixWord ++ tailWord_3360451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360451).length < 2 ^ (prefixWord ++ tailWord_3360451).sum := by decide
  have hdescent : baseEnd_3360451 < baseStart_3360451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360464 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 6]
def baseStart_3360464 : Nat := 118140960795 + 3360464 * 2 ^ 59
def prefixEnd_3360464 : Nat := 4983230072969 + 3 ^ 40 * 3360464 * 2
def baseEnd_3360464 : Nat := 1725533254130645402845513

theorem tailTrace_3360464 : CollatzResearch.WordTrace tailWord_3360464 prefixEnd_3360464 1725533254130645402845513 := by
  unfold tailWord_3360464
  simp only [CollatzResearch.WordTrace]
  refine ⟨61283095648810162202040223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81710794198413549602720297 61283095648810162202040223)
  ·
    refine ⟨91924643473215243303060335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61283095648810162202040223 91924643473215243303060335)
    ·
      refine ⟨137886965209822864954590503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91924643473215243303060335 137886965209822864954590503)
      ·
        refine ⟨206830447814734297431885755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137886965209822864954590503 206830447814734297431885755)
        ·
          refine ⟨310245671722101446147828633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206830447814734297431885755 310245671722101446147828633)
          ·
            refine ⟨232684253791576084610871475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310245671722101446147828633 232684253791576084610871475)
            ·
              refine ⟨349026380687364126916307213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232684253791576084610871475 349026380687364126916307213)
              ·
                refine ⟨130884892757761547593615205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349026380687364126916307213 130884892757761547593615205)
                ·
                  refine ⟨24540917392080290173802851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130884892757761547593615205 24540917392080290173802851)
                  ·
                    refine ⟨36811376088120435260704277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24540917392080290173802851 36811376088120435260704277)
                    ·
                      refine ⟨1725533254130645402845513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36811376088120435260704277 1725533254130645402845513)
                      ·
                        rfl

theorem cell23_3360464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_3360464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360464 prefixEnd_3360464 := by exact prefixLift 3360464
  have htrace : WordTrace (prefixWord ++ tailWord_3360464) baseStart_3360464 baseEnd_3360464 := by
    simpa [prefixWord, tailWord_3360464, baseEnd_3360464] using wordTrace_append hprefix tailTrace_3360464
  have hstable : (prefixWord ++ tailWord_3360464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360464).length < 2 ^ (prefixWord ++ tailWord_3360464).sum := by decide
  have hdescent : baseEnd_3360464 < baseStart_3360464 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360471 : List Nat := [1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 3]
def baseStart_3360471 : Nat := 118140960795 + 3360471 * 2 ^ 59
def prefixEnd_3360471 : Nat := 4983230072969 + 3 ^ 40 * 3360471 * 2
def baseEnd_3360471 : Nat := 1725536848495226875457981

theorem tailTrace_3360471 : CollatzResearch.WordTrace tailWord_3360471 prefixEnd_3360471 1725536848495226875457981 := by
  unfold tailWord_3360471
  simp only [CollatzResearch.WordTrace]
  refine ⟨122566446608594964599585267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81710964405729976399723511 122566446608594964599585267)
  ·
    refine ⟨183849669912892446899377901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122566446608594964599585267 183849669912892446899377901)
    ·
      refine ⟨68943626217334667587266713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183849669912892446899377901 68943626217334667587266713)
      ·
        refine ⟨51707719663001000690450035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68943626217334667587266713 51707719663001000690450035)
        ·
          refine ⟨77561579494501501035675053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51707719663001000690450035 77561579494501501035675053)
          ·
            refine ⟨29085592310438062888378145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77561579494501501035675053 29085592310438062888378145)
            ·
              refine ⟨21814194232828547166283609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29085592310438062888378145 21814194232828547166283609)
              ·
                refine ⟨16360645674621410374712707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21814194232828547166283609 16360645674621410374712707)
                ·
                  refine ⟨24540968511932115562069061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16360645674621410374712707 24540968511932115562069061)
                  ·
                    refine ⟨4601431595987271667887949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24540968511932115562069061 4601431595987271667887949)
                    ·
                      refine ⟨1725536848495226875457981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4601431595987271667887949 1725536848495226875457981)
                      ·
                        rfl

theorem cell23_3360471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 2, 1, 4, 3].length) (baseStart_3360471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360471 prefixEnd_3360471 := by exact prefixLift 3360471
  have htrace : WordTrace (prefixWord ++ tailWord_3360471) baseStart_3360471 baseEnd_3360471 := by
    simpa [prefixWord, tailWord_3360471, baseEnd_3360471] using wordTrace_append hprefix tailTrace_3360471
  have hstable : (prefixWord ++ tailWord_3360471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360471).length < 2 ^ (prefixWord ++ tailWord_3360471).sum := by decide
  have hdescent : baseEnd_3360471 < baseStart_3360471 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360488 : List Nat := [2, 1, 4, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_3360488 : Nat := 118140960795 + 3360488 * 2 ^ 59
def prefixEnd_3360488 : Nat := 4983230072969 + 3 ^ 40 * 3360488 * 2
def baseEnd_3360488 : Nat := 1725545577666353308945403

theorem tailTrace_3360488 : CollatzResearch.WordTrace tailWord_3360488 prefixEnd_3360488 1725545577666353308945403 := by
  unfold tailWord_3360488
  simp only [CollatzResearch.WordTrace]
  refine ⟨61283533324766688251477059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81711377766355584335302745 61283533324766688251477059)
  ·
    refine ⟨91925299987150032377215589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61283533324766688251477059 91925299987150032377215589)
    ·
      refine ⟨17235993747590631070727923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91925299987150032377215589 17235993747590631070727923)
      ·
        refine ⟨25853990621385946606091885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17235993747590631070727923 25853990621385946606091885)
        ·
          refine ⟨9695246483019729977284457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25853990621385946606091885 9695246483019729977284457)
          ·
            refine ⟨7271434862264797482963343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9695246483019729977284457 7271434862264797482963343)
            ·
              refine ⟨10907152293397196224445015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271434862264797482963343 10907152293397196224445015)
              ·
                refine ⟨16360728440095794336667523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10907152293397196224445015 16360728440095794336667523)
                ·
                  refine ⟨24541092660143691505001285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16360728440095794336667523 24541092660143691505001285)
                  ·
                    refine ⟨4601454873776942157187741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24541092660143691505001285 4601454873776942157187741)
                    ·
                      refine ⟨1725545577666353308945403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4601454873776942157187741 1725545577666353308945403)
                      ·
                        rfl

theorem cell23_3360488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_3360488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360488 prefixEnd_3360488 := by exact prefixLift 3360488
  have htrace : WordTrace (prefixWord ++ tailWord_3360488) baseStart_3360488 baseEnd_3360488 := by
    simpa [prefixWord, tailWord_3360488, baseEnd_3360488] using wordTrace_append hprefix tailTrace_3360488
  have hstable : (prefixWord ++ tailWord_3360488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360488).length < 2 ^ (prefixWord ++ tailWord_3360488).sum := by decide
  have hdescent : baseEnd_3360488 < baseStart_3360488 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360495 : List Nat := [1, 1, 2, 1, 5, 1, 4, 3, 1, 4]
def baseStart_3360495 : Nat := 118140960795 + 3360495 * 2 ^ 59
def prefixEnd_3360495 : Nat := 4983230072969 + 3 ^ 40 * 3360495 * 2
def baseEnd_3360495 : Nat := 575183057343644927185957

theorem tailTrace_3360495 : CollatzResearch.WordTrace tailWord_3360495 prefixEnd_3360495 575183057343644927185957 := by
  unfold tailWord_3360495
  simp only [CollatzResearch.WordTrace]
  refine ⟨122567321960508016698458939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81711547973672011132305959 122567321960508016698458939)
  ·
    refine ⟨183850982940762025047688409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122567321960508016698458939 183850982940762025047688409)
    ·
      refine ⟨137888237205571518785766307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183850982940762025047688409 137888237205571518785766307)
      ·
        refine ⟨206832355808357278178649461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137888237205571518785766307 206832355808357278178649461)
        ·
          refine ⟨19390533357033494829248387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206832355808357278178649461 19390533357033494829248387)
          ·
            refine ⟨29085800035550242243872581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19390533357033494829248387 29085800035550242243872581)
            ·
              refine ⟨5453587506665670420726109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29085800035550242243872581 5453587506665670420726109)
              ·
                refine ⟨2045095314999626407772291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5453587506665670420726109 2045095314999626407772291)
                ·
                  refine ⟨3067642972499439611658437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045095314999626407772291 3067642972499439611658437)
                  ·
                    refine ⟨575183057343644927185957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3067642972499439611658437 575183057343644927185957)
                    ·
                      rfl

theorem cell23_3360495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 4, 3, 1, 4].length) (baseStart_3360495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360495 prefixEnd_3360495 := by exact prefixLift 3360495
  have htrace : WordTrace (prefixWord ++ tailWord_3360495) baseStart_3360495 baseEnd_3360495 := by
    simpa [prefixWord, tailWord_3360495, baseEnd_3360495] using wordTrace_append hprefix tailTrace_3360495
  have hstable : (prefixWord ++ tailWord_3360495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360495).length < 2 ^ (prefixWord ++ tailWord_3360495).sum := by decide
  have hdescent : baseEnd_3360495 < baseStart_3360495 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360535 : List Nat := [1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3360535 : Nat := 118140960795 + 3360535 * 2 ^ 59
def prefixEnd_3360535 : Nat := 4983230072969 + 3 ^ 40 * 3360535 * 2
def baseEnd_3360535 : Nat := 1725569711257114625057687

theorem tailTrace_3360535 : CollatzResearch.WordTrace tailWord_3360535 prefixEnd_3360535 1725569711257114625057687 := by
  unfold tailWord_3360535
  simp only [CollatzResearch.WordTrace]
  refine ⟨122568780880363103529915059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81712520586908735686610039 122568780880363103529915059)
  ·
    refine ⟨183853171320544655294872589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122568780880363103529915059 183853171320544655294872589)
    ·
      refine ⟨68944939245204245735577221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183853171320544655294872589 68944939245204245735577221)
      ·
        refine ⟨12927176108475796075420729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68944939245204245735577221 12927176108475796075420729)
        ·
          refine ⟨9695382081356847056565547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12927176108475796075420729 9695382081356847056565547)
          ·
            refine ⟨14543073122035270584848321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9695382081356847056565547 14543073122035270584848321)
            ·
              refine ⟨10907304841526452938636241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14543073122035270584848321 10907304841526452938636241)
              ·
                refine ⟨8180478631144839703977181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10907304841526452938636241 8180478631144839703977181)
                ·
                  refine ⟨3067679486679314888991443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8180478631144839703977181 3067679486679314888991443)
                  ·
                    refine ⟨4601519230018972333487165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3067679486679314888991443 4601519230018972333487165)
                    ·
                      refine ⟨1725569711257114625057687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4601519230018972333487165 1725569711257114625057687)
                      ·
                        rfl

theorem cell23_3360535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3360535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360535 prefixEnd_3360535 := by exact prefixLift 3360535
  have htrace : WordTrace (prefixWord ++ tailWord_3360535) baseStart_3360535 baseEnd_3360535 := by
    simpa [prefixWord, tailWord_3360535, baseEnd_3360535] using wordTrace_append hprefix tailTrace_3360535
  have hstable : (prefixWord ++ tailWord_3360535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360535).length < 2 ^ (prefixWord ++ tailWord_3360535).sum := by decide
  have hdescent : baseEnd_3360535 < baseStart_3360535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360538 : List Nat := [3, 1, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_3360538 : Nat := 118140960795 + 3360538 * 2 ^ 59
def prefixEnd_3360538 : Nat := 4983230072969 + 3 ^ 40 * 3360538 * 2
def baseEnd_3360538 : Nat := 575190417233026037773391

theorem tailTrace_3360538 : CollatzResearch.WordTrace tailWord_3360538 prefixEnd_3360538 575190417233026037773391 := by
  unfold tailWord_3360538
  simp only [CollatzResearch.WordTrace]
  refine ⟨30642222574838058760568567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81712593532901490028182845 30642222574838058760568567)
  ·
    refine ⟨45963333862257088140852851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30642222574838058760568567 45963333862257088140852851)
    ·
      refine ⟨68945000793385632211279277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45963333862257088140852851 68945000793385632211279277)
      ·
        refine ⟨25854375297519612079229729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68945000793385632211279277 25854375297519612079229729)
        ·
          refine ⟨19390781473139709059422297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25854375297519612079229729 19390781473139709059422297)
          ·
            refine ⟨14543086104854781794566723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19390781473139709059422297 14543086104854781794566723)
            ·
              refine ⟨21814629157282172691850085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14543086104854781794566723 21814629157282172691850085)
              ·
                refine ⟨4090242966990407379721891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21814629157282172691850085 4090242966990407379721891)
                ·
                  refine ⟨6135364450485611069582837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090242966990407379721891 6135364450485611069582837)
                  ·
                    refine ⟨575190417233026037773391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6135364450485611069582837 575190417233026037773391)
                    ·
                      rfl

theorem cell23_3360538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_3360538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360538 prefixEnd_3360538 := by exact prefixLift 3360538
  have htrace : WordTrace (prefixWord ++ tailWord_3360538) baseStart_3360538 baseEnd_3360538 := by
    simpa [prefixWord, tailWord_3360538, baseEnd_3360538] using wordTrace_append hprefix tailTrace_3360538
  have hstable : (prefixWord ++ tailWord_3360538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360538).length < 2 ^ (prefixWord ++ tailWord_3360538).sum := by decide
  have hdescent : baseEnd_3360538 < baseStart_3360538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360568 : List Nat := [2, 1, 2, 1, 3, 3, 2, 1, 4, 4]
def baseStart_3360568 : Nat := 118140960795 + 3360568 * 2 ^ 59
def prefixEnd_3360568 : Nat := 4983230072969 + 3 ^ 40 * 3360568 * 2
def baseEnd_3360568 : Nat := 575195552039570998648345

theorem tailTrace_3360568 : CollatzResearch.WordTrace tailWord_3360568 prefixEnd_3360568 575195552039570998648345 := by
  unfold tailWord_3360568
  simp only [CollatzResearch.WordTrace]
  refine ⟨61284992244621775082933179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81713322992829033443910905 61284992244621775082933179)
  ·
    refine ⟨91927488366932662624399769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61284992244621775082933179 91927488366932662624399769)
    ·
      refine ⟨68945616275199496968299827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91927488366932662624399769 68945616275199496968299827)
      ·
        refine ⟨103418424412799245452449741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68945616275199496968299827 103418424412799245452449741)
        ·
          refine ⟨38781909154799717044668653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103418424412799245452449741 38781909154799717044668653)
          ·
            refine ⟨14543215933049893891750745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38781909154799717044668653 14543215933049893891750745)
            ·
              refine ⟨10907411949787420418813059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14543215933049893891750745 10907411949787420418813059)
              ·
                refine ⟨16361117924681130628219589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10907411949787420418813059 16361117924681130628219589)
                ·
                  refine ⟨3067709610877711992791173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16361117924681130628219589 3067709610877711992791173)
                  ·
                    refine ⟨575195552039570998648345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3067709610877711992791173 575195552039570998648345)
                    ·
                      rfl

theorem cell23_3360568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_3360568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360568 prefixEnd_3360568 := by exact prefixLift 3360568
  have htrace : WordTrace (prefixWord ++ tailWord_3360568) baseStart_3360568 baseEnd_3360568 := by
    simpa [prefixWord, tailWord_3360568, baseEnd_3360568] using wordTrace_append hprefix tailTrace_3360568
  have hstable : (prefixWord ++ tailWord_3360568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360568).length < 2 ^ (prefixWord ++ tailWord_3360568).sum := by decide
  have hdescent : baseEnd_3360568 < baseStart_3360568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360569 : List Nat := [1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3360569 : Nat := 118140960795 + 3360569 * 2 ^ 59
def prefixEnd_3360569 : Nat := 4983230072969 + 3 ^ 40 * 3360569 * 2
def baseEnd_3360569 : Nat := 1725587169599367492032531

theorem tailTrace_3360569 : CollatzResearch.WordTrace tailWord_3360569 prefixEnd_3360569 1725587169599367492032531 := by
  unfold tailWord_3360569
  simp only [CollatzResearch.WordTrace]
  refine ⟨122570020962239927336652761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81713347308159951557768507 122570020962239927336652761)
  ·
    refine ⟨91927515721679945502489571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122570020962239927336652761 91927515721679945502489571)
    ·
      refine ⟨137891273582519918253734357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91927515721679945502489571 137891273582519918253734357)
      ·
        refine ⟨3231826724590310584071899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 137891273582519918253734357 3231826724590310584071899)
        ·
          refine ⟨4847740086885465876107849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3231826724590310584071899 4847740086885465876107849)
          ·
            refine ⟨3635805065164099407080887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4847740086885465876107849 3635805065164099407080887)
            ·
              refine ⟨5453707597746149110621331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635805065164099407080887 5453707597746149110621331)
              ·
                refine ⟨8180561396619223665931997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453707597746149110621331 8180561396619223665931997)
                ·
                  refine ⟨3067710523732208874724499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8180561396619223665931997 3067710523732208874724499)
                  ·
                    refine ⟨4601565785598313312086749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3067710523732208874724499 4601565785598313312086749)
                    ·
                      refine ⟨1725587169599367492032531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4601565785598313312086749 1725587169599367492032531)
                      ·
                        rfl

theorem cell23_3360569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3360569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360569 prefixEnd_3360569 := by exact prefixLift 3360569
  have htrace : WordTrace (prefixWord ++ tailWord_3360569) baseStart_3360569 baseEnd_3360569 := by
    simpa [prefixWord, tailWord_3360569, baseEnd_3360569] using wordTrace_append hprefix tailTrace_3360569
  have hstable : (prefixWord ++ tailWord_3360569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360569).length < 2 ^ (prefixWord ++ tailWord_3360569).sum := by decide
  have hdescent : baseEnd_3360569 < baseStart_3360569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360581 : List Nat := [1, 3, 1, 1, 1, 2, 6, 8]
def baseStart_3360581 : Nat := 118140960795 + 3360581 * 2 ^ 59
def prefixEnd_3360581 : Nat := 4983230072969 + 3 ^ 40 * 3360581 * 2
def baseEnd_3360581 : Nat := 63910864124711905373425

theorem tailTrace_3360581 : CollatzResearch.WordTrace tailWord_3360581 prefixEnd_3360581 63910864124711905373425 := by
  unfold tailWord_3360581
  simp only [CollatzResearch.WordTrace]
  refine ⟨122570458638196453386089597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81713639092130968924059731 122570458638196453386089597)
  ·
    refine ⟨45963921989323670019783599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122570458638196453386089597 45963921989323670019783599)
    ·
      refine ⟨68945882983985505029675399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45963921989323670019783599 68945882983985505029675399)
      ·
        refine ⟨103418824475978257544513099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68945882983985505029675399 103418824475978257544513099)
        ·
          refine ⟨155128236713967386316769649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103418824475978257544513099 155128236713967386316769649)
          ·
            refine ⟨116346177535475539737577237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155128236713967386316769649 116346177535475539737577237)
            ·
              refine ⟨5453727071975415925198933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116346177535475539737577237 5453727071975415925198933)
              ·
                refine ⟨63910864124711905373425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5453727071975415925198933 63910864124711905373425)
                ·
                  rfl

theorem cell23_3360581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 8].length) (baseStart_3360581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360581 prefixEnd_3360581 := by exact prefixLift 3360581
  have htrace : WordTrace (prefixWord ++ tailWord_3360581) baseStart_3360581 baseEnd_3360581 := by
    simpa [prefixWord, tailWord_3360581, baseEnd_3360581] using wordTrace_append hprefix tailTrace_3360581
  have hstable : (prefixWord ++ tailWord_3360581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360581).length < 2 ^ (prefixWord ++ tailWord_3360581).sum := by decide
  have hdescent : baseEnd_3360581 < baseStart_3360581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360608 : List Nat := [2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 3]
def baseStart_3360608 : Nat := 118140960795 + 3360608 * 2 ^ 59
def prefixEnd_3360608 : Nat := 4983230072969 + 3 ^ 40 * 3360608 * 2
def baseEnd_3360608 : Nat := 1725607195344892839444851

theorem tailTrace_3360608 : CollatzResearch.WordTrace tailWord_3360608 prefixEnd_3360608 1725607195344892839444851 := by
  unfold tailWord_3360608
  simp only [CollatzResearch.WordTrace]
  refine ⟨61285721704549318498661239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81714295606065757998214985 61285721704549318498661239)
  ·
    refine ⟨91928582556823977747991859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61285721704549318498661239 91928582556823977747991859)
    ·
      refine ⟨137892873835235966621987789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91928582556823977747991859 137892873835235966621987789)
      ·
        refine ⟨51709827688213487483245421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137892873835235966621987789 51709827688213487483245421)
        ·
          refine ⟨19391185383080057806217033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51709827688213487483245421 19391185383080057806217033)
          ·
            refine ⟨14543389037310043354662775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19391185383080057806217033 14543389037310043354662775)
            ·
              refine ⟨21815083555965065031994163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14543389037310043354662775 21815083555965065031994163)
              ·
                refine ⟨32722625333947597547991245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21815083555965065031994163 32722625333947597547991245)
                ·
                  refine ⟨12270984500230349080496717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32722625333947597547991245 12270984500230349080496717)
                  ·
                    refine ⟨4601619187586380905186269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12270984500230349080496717 4601619187586380905186269)
                    ·
                      refine ⟨1725607195344892839444851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4601619187586380905186269 1725607195344892839444851)
                      ·
                        rfl

theorem cell23_3360608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 3].length) (baseStart_3360608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360608 prefixEnd_3360608 := by exact prefixLift 3360608
  have htrace : WordTrace (prefixWord ++ tailWord_3360608) baseStart_3360608 baseEnd_3360608 := by
    simpa [prefixWord, tailWord_3360608, baseEnd_3360608] using wordTrace_append hprefix tailTrace_3360608
  have hstable : (prefixWord ++ tailWord_3360608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360608).length < 2 ^ (prefixWord ++ tailWord_3360608).sum := by decide
  have hdescent : baseEnd_3360608 < baseStart_3360608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360612 : List Nat := [2, 3, 1, 1, 6, 1, 1, 1, 1, 1, 5]
def baseStart_3360612 : Nat := 118140960795 + 3360612 * 2 ^ 59
def prefixEnd_3360612 : Nat := 4983230072969 + 3 ^ 40 * 3360612 * 2
def baseEnd_3360612 : Nat := 1725609249267510823794833

theorem tailTrace_3360612 : CollatzResearch.WordTrace tailWord_3360612 prefixEnd_3360612 1725609249267510823794833 := by
  unfold tailWord_3360612
  simp only [CollatzResearch.WordTrace]
  refine ⟨61285794650542072840234045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81714392867389430453645393 61285794650542072840234045)
  ·
    refine ⟨22982172993953277315087767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61285794650542072840234045 22982172993953277315087767)
    ·
      refine ⟨34473259490929915972631651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22982172993953277315087767 34473259490929915972631651)
      ·
        refine ⟨51709889236394873958947477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34473259490929915972631651 51709889236394873958947477)
        ·
          refine ⟨2423901057956009716825663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51709889236394873958947477 2423901057956009716825663)
          ·
            refine ⟨3635851586934014575238495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423901057956009716825663 3635851586934014575238495)
            ·
              refine ⟨5453777380401021862857743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635851586934014575238495 5453777380401021862857743)
              ·
                refine ⟨8180666070601532794286615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453777380401021862857743 8180666070601532794286615)
                ·
                  refine ⟨12270999105902299191429923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8180666070601532794286615 12270999105902299191429923)
                  ·
                    refine ⟨18406498658853448787144885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12270999105902299191429923 18406498658853448787144885)
                    ·
                      refine ⟨1725609249267510823794833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18406498658853448787144885 1725609249267510823794833)
                      ·
                        rfl

theorem cell23_3360612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 1, 1, 1, 5].length) (baseStart_3360612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360612 prefixEnd_3360612 := by exact prefixLift 3360612
  have htrace : WordTrace (prefixWord ++ tailWord_3360612) baseStart_3360612 baseEnd_3360612 := by
    simpa [prefixWord, tailWord_3360612, baseEnd_3360612] using wordTrace_append hprefix tailTrace_3360612
  have hstable : (prefixWord ++ tailWord_3360612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360612).length < 2 ^ (prefixWord ++ tailWord_3360612).sum := by decide
  have hdescent : baseEnd_3360612 < baseStart_3360612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360665 : List Nat := [1, 2, 1, 2, 1, 3, 4, 2, 1, 4, 2]
def baseStart_3360665 : Nat := 118140960795 + 3360665 * 2 ^ 59
def prefixEnd_3360665 : Nat := 4983230072969 + 3 ^ 40 * 3360665 * 2
def baseEnd_3360665 : Nat := 1725636463742199116432089

theorem tailTrace_3360665 : CollatzResearch.WordTrace tailWord_3360665 prefixEnd_3360665 1725636463742199116432089 := by
  unfold tailWord_3360665
  simp only [CollatzResearch.WordTrace]
  refine ⟨122573522369892135732147449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81715681579928090488098299 122573522369892135732147449)
  ·
    refine ⟨91930141777419101799110587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122573522369892135732147449 91930141777419101799110587)
    ·
      refine ⟨137895212666128652698665881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91930141777419101799110587 137895212666128652698665881)
      ·
        refine ⟨103421409499596489523999411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137895212666128652698665881 103421409499596489523999411)
        ·
          refine ⟨155132114249394734285999117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103421409499596489523999411 155132114249394734285999117)
          ·
            refine ⟨58174542843523025357249669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155132114249394734285999117 58174542843523025357249669)
            ·
              refine ⟨10907726783160567254484313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58174542843523025357249669 10907726783160567254484313)
              ·
                refine ⟨8180795087370425440863235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10907726783160567254484313 8180795087370425440863235)
                ·
                  refine ⟨12271192631055638161294853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8180795087370425440863235 12271192631055638161294853)
                  ·
                    refine ⟨2300848618322932155242785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12271192631055638161294853 2300848618322932155242785)
                    ·
                      refine ⟨1725636463742199116432089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300848618322932155242785 1725636463742199116432089)
                      ·
                        rfl

theorem cell23_3360665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_3360665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360665 prefixEnd_3360665 := by exact prefixLift 3360665
  have htrace : WordTrace (prefixWord ++ tailWord_3360665) baseStart_3360665 baseEnd_3360665 := by
    simpa [prefixWord, tailWord_3360665, baseEnd_3360665] using wordTrace_append hprefix tailTrace_3360665
  have hstable : (prefixWord ++ tailWord_3360665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360665).length < 2 ^ (prefixWord ++ tailWord_3360665).sum := by decide
  have hdescent : baseEnd_3360665 < baseStart_3360665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360669 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_3360669 : Nat := 118140960795 + 3360669 * 2 ^ 59
def prefixEnd_3360669 : Nat := 4983230072969 + 3 ^ 40 * 3360669 * 2
def baseEnd_3360669 : Nat := 1725638517664817100782071

theorem tailTrace_3360669 : CollatzResearch.WordTrace tailWord_3360669 prefixEnd_3360669 1725638517664817100782071 := by
  unfold tailWord_3360669
  simp only [CollatzResearch.WordTrace]
  refine ⟨122573668261877644415293061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81715778841251762943528707 122573668261877644415293061)
  ·
    refine ⟨22982562799102058327867449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122573668261877644415293061 22982562799102058327867449)
    ·
      refine ⟨17236922099326543745900587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22982562799102058327867449 17236922099326543745900587)
      ·
        refine ⟨25855383148989815618850881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17236922099326543745900587 25855383148989815618850881)
        ·
          refine ⟨19391537361742361714138161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25855383148989815618850881 19391537361742361714138161)
          ·
            refine ⟨14543653021306771285603621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19391537361742361714138161 14543653021306771285603621)
            ·
              refine ⟨2726934941495019616050679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14543653021306771285603621 2726934941495019616050679)
              ·
                refine ⟨4090402412242529424076019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726934941495019616050679 4090402412242529424076019)
                ·
                  refine ⟨6135603618363794136114029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4090402412242529424076019 6135603618363794136114029)
                  ·
                    refine ⟨2300851356886422801042761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6135603618363794136114029 2300851356886422801042761)
                    ·
                      refine ⟨1725638517664817100782071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300851356886422801042761 1725638517664817100782071)
                      ·
                        rfl

theorem cell23_3360669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_3360669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360669 prefixEnd_3360669 := by exact prefixLift 3360669
  have htrace : WordTrace (prefixWord ++ tailWord_3360669) baseStart_3360669 baseEnd_3360669 := by
    simpa [prefixWord, tailWord_3360669, baseEnd_3360669] using wordTrace_append hprefix tailTrace_3360669
  have hstable : (prefixWord ++ tailWord_3360669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360669).length < 2 ^ (prefixWord ++ tailWord_3360669).sum := by decide
  have hdescent : baseEnd_3360669 < baseStart_3360669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360681 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_3360681 : Nat := 118140960795 + 3360681 * 2 ^ 59
def prefixEnd_3360681 : Nat := 4983230072969 + 3 ^ 40 * 3360681 * 2
def baseEnd_3360681 : Nat := 1725644679432671053832015

theorem tailTrace_3360681 : CollatzResearch.WordTrace tailWord_3360681 prefixEnd_3360681 1725644679432671053832015 := by
  unfold tailWord_3360681
  simp only [CollatzResearch.WordTrace]
  refine ⟨122574105937834170464729897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81716070625222780309819931 122574105937834170464729897)
  ·
    refine ⟨91930579453375627848547423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122574105937834170464729897 91930579453375627848547423)
    ·
      refine ⟨137895869180063441772821135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91930579453375627848547423 137895869180063441772821135)
      ·
        refine ⟨206843803770095162659231703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137895869180063441772821135 206843803770095162659231703)
        ·
          refine ⟨310265705655142743988847555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206843803770095162659231703 310265705655142743988847555)
          ·
            refine ⟨465398558482714115983271333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310265705655142743988847555 465398558482714115983271333)
            ·
              refine ⟨87262229715508896746863375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 465398558482714115983271333 87262229715508896746863375)
              ·
                refine ⟨130893344573263345120295063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87262229715508896746863375 130893344573263345120295063)
                ·
                  refine ⟨196340016859895017680442595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130893344573263345120295063 196340016859895017680442595)
                  ·
                    refine ⟨294510025289842526520663893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 196340016859895017680442595 294510025289842526520663893)
                    ·
                      refine ⟨1725644679432671053832015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 294510025289842526520663893 1725644679432671053832015)
                      ·
                        rfl

theorem cell23_3360681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_3360681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360681 prefixEnd_3360681 := by exact prefixLift 3360681
  have htrace : WordTrace (prefixWord ++ tailWord_3360681) baseStart_3360681 baseEnd_3360681 := by
    simpa [prefixWord, tailWord_3360681, baseEnd_3360681] using wordTrace_append hprefix tailTrace_3360681
  have hstable : (prefixWord ++ tailWord_3360681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360681).length < 2 ^ (prefixWord ++ tailWord_3360681).sum := by decide
  have hdescent : baseEnd_3360681 < baseStart_3360681 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360698 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_3360698 : Nat := 118140960795 + 3360698 * 2 ^ 59
def prefixEnd_3360698 : Nat := 4983230072969 + 3 ^ 40 * 3360698 * 2
def baseEnd_3360698 : Nat := 1725653408603797487319437

theorem tailTrace_3360698 : CollatzResearch.WordTrace tailWord_3360698 prefixEnd_3360698 1725653408603797487319437 := by
  unfold tailWord_3360698
  simp only [CollatzResearch.WordTrace]
  refine ⟨30643681494693145592024687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81716483985848388245399165 30643681494693145592024687)
  ·
    refine ⟨45965522242039718388037031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30643681494693145592024687 45965522242039718388037031)
    ·
      refine ⟨68948283363059577582055547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45965522242039718388037031 68948283363059577582055547)
      ·
        refine ⟨103422425044589366373083321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68948283363059577582055547 103422425044589366373083321)
        ·
          refine ⟨77566818783442024779812491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103422425044589366373083321 77566818783442024779812491)
          ·
            refine ⟨116350228175163037169718737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77566818783442024779812491 116350228175163037169718737)
            ·
              refine ⟨87262671131372277877289053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116350228175163037169718737 87262671131372277877289053)
              ·
                refine ⟨32723501674264604203983395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87262671131372277877289053 32723501674264604203983395)
                ·
                  refine ⟨49085252511396906305975093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32723501674264604203983395 49085252511396906305975093)
                  ·
                    refine ⟨4601742422943459966185165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49085252511396906305975093 4601742422943459966185165)
                    ·
                      refine ⟨1725653408603797487319437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4601742422943459966185165 1725653408603797487319437)
                      ·
                        rfl

theorem cell23_3360698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_3360698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360698 prefixEnd_3360698 := by exact prefixLift 3360698
  have htrace : WordTrace (prefixWord ++ tailWord_3360698) baseStart_3360698 baseEnd_3360698 := by
    simpa [prefixWord, tailWord_3360698, baseEnd_3360698] using wordTrace_append hprefix tailTrace_3360698
  have hstable : (prefixWord ++ tailWord_3360698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360698).length < 2 ^ (prefixWord ++ tailWord_3360698).sum := by decide
  have hdescent : baseEnd_3360698 < baseStart_3360698 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360718 : List Nat := [4, 1, 1, 1, 2, 2, 1, 3, 1, 7]
def baseStart_3360718 : Nat := 118140960795 + 3360718 * 2 ^ 59
def prefixEnd_3360718 : Nat := 4983230072969 + 3 ^ 40 * 3360718 * 2
def baseEnd_3360718 : Nat := 575221226072295803023115

theorem tailTrace_3360718 : CollatzResearch.WordTrace tailWord_3360718 prefixEnd_3360718 575221226072295803023115 := by
  unfold tailWord_3360718
  simp only [CollatzResearch.WordTrace]
  refine ⟨15321931929837515722978351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81716970292466750522551205 15321931929837515722978351)
  ·
    refine ⟨22982897894756273584467527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15321931929837515722978351 22982897894756273584467527)
    ·
      refine ⟨34474346842134410376701291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22982897894756273584467527 34474346842134410376701291)
      ·
        refine ⟨51711520263201615565051937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34474346842134410376701291 51711520263201615565051937)
        ·
          refine ⟨38783640197401211673788953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51711520263201615565051937 38783640197401211673788953)
          ·
            refine ⟨29087730148050908755341715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38783640197401211673788953 29087730148050908755341715)
            ·
              refine ⟨43631595222076363133012573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29087730148050908755341715 43631595222076363133012573)
              ·
                refine ⟨16361848208278636174879715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43631595222076363133012573 16361848208278636174879715)
                ·
                  refine ⟨24542772312417954262319573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16361848208278636174879715 24542772312417954262319573)
                  ·
                    refine ⟨575221226072295803023115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24542772312417954262319573 575221226072295803023115)
                    ·
                      rfl

theorem cell23_3360718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 3, 1, 7].length) (baseStart_3360718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360718 prefixEnd_3360718 := by exact prefixLift 3360718
  have htrace : WordTrace (prefixWord ++ tailWord_3360718) baseStart_3360718 baseEnd_3360718 := by
    simpa [prefixWord, tailWord_3360718, baseEnd_3360718] using wordTrace_append hprefix tailTrace_3360718
  have hstable : (prefixWord ++ tailWord_3360718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360718).length < 2 ^ (prefixWord ++ tailWord_3360718).sum := by decide
  have hdescent : baseEnd_3360718 < baseStart_3360718 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360728 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_3360728 : Nat := 118140960795 + 3360728 * 2 ^ 59
def prefixEnd_3360728 : Nat := 4983230072969 + 3 ^ 40 * 3360728 * 2
def baseEnd_3360728 : Nat := 1725668813023432369944299

theorem tailTrace_3360728 : CollatzResearch.WordTrace tailWord_3360728 prefixEnd_3360728 1725668813023432369944299 := by
  unfold tailWord_3360728
  simp only [CollatzResearch.WordTrace]
  refine ⟨61287910084331948745845419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81717213445775931661127225 61287910084331948745845419)
  ·
    refine ⟨91931865126497923118768129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61287910084331948745845419 91931865126497923118768129)
    ·
      refine ⟨68948898844873442339076097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91931865126497923118768129 68948898844873442339076097)
      ·
        refine ⟨51711674133655081754307073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68948898844873442339076097 51711674133655081754307073)
        ·
          refine ⟨38783755600241311315730305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51711674133655081754307073 38783755600241311315730305)
          ·
            refine ⟨29087816700180983486797729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38783755600241311315730305 29087816700180983486797729)
            ·
              refine ⟨21815862525135737615098297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29087816700180983486797729 21815862525135737615098297)
              ·
                refine ⟨16361896893851803211323723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21815862525135737615098297 16361896893851803211323723)
                ·
                  refine ⟨24542845340777704816985585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16361896893851803211323723 24542845340777704816985585)
                  ·
                    refine ⟨18407134005583278612739189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24542845340777704816985585 18407134005583278612739189)
                    ·
                      refine ⟨1725668813023432369944299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18407134005583278612739189 1725668813023432369944299)
                      ·
                        rfl

theorem cell23_3360728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_3360728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360728 prefixEnd_3360728 := by exact prefixLift 3360728
  have htrace : WordTrace (prefixWord ++ tailWord_3360728) baseStart_3360728 baseEnd_3360728 := by
    simpa [prefixWord, tailWord_3360728, baseEnd_3360728] using wordTrace_append hprefix tailTrace_3360728
  have hstable : (prefixWord ++ tailWord_3360728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360728).length < 2 ^ (prefixWord ++ tailWord_3360728).sum := by decide
  have hdescent : baseEnd_3360728 < baseStart_3360728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360735 : List Nat := [1, 1, 2, 3, 4, 2, 1, 2, 2, 5]
def baseStart_3360735 : Nat := 118140960795 + 3360735 * 2 ^ 59
def prefixEnd_3360735 : Nat := 4983230072969 + 3 ^ 40 * 3360735 * 2
def baseEnd_3360735 : Nat := 575224135796004614185589

theorem tailTrace_3360735 : CollatzResearch.WordTrace tailWord_3360735 prefixEnd_3360735 575224135796004614185589 := by
  unfold tailWord_3360735
  simp only [CollatzResearch.WordTrace]
  refine ⟨122576075479638537687195659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81717383653092358458130439 122576075479638537687195659)
  ·
    refine ⟨183864113219457806530793489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122576075479638537687195659 183864113219457806530793489)
    ·
      refine ⟨137898084914593354898095117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183864113219457806530793489 137898084914593354898095117)
      ·
        refine ⟨51711781842972508086785669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137898084914593354898095117 51711781842972508086785669)
        ·
          refine ⟨9695959095557345266272313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51711781842972508086785669 9695959095557345266272313)
          ·
            refine ⟨7271969321668008949704235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9695959095557345266272313 7271969321668008949704235)
            ·
              refine ⟨10907953982502013424556353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7271969321668008949704235 10907953982502013424556353)
              ·
                refine ⟨8180965486876510068417265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10907953982502013424556353 8180965486876510068417265)
                ·
                  refine ⟨6135724115157382551312949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8180965486876510068417265 6135724115157382551312949)
                  ·
                    refine ⟨575224135796004614185589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6135724115157382551312949 575224135796004614185589)
                    ·
                      rfl

theorem cell23_3360735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_3360735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360735 prefixEnd_3360735 := by exact prefixLift 3360735
  have htrace : WordTrace (prefixWord ++ tailWord_3360735) baseStart_3360735 baseEnd_3360735 := by
    simpa [prefixWord, tailWord_3360735, baseEnd_3360735] using wordTrace_append hprefix tailTrace_3360735
  have hstable : (prefixWord ++ tailWord_3360735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360735).length < 2 ^ (prefixWord ++ tailWord_3360735).sum := by decide
  have hdescent : baseEnd_3360735 < baseStart_3360735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360755 : List Nat := [1, 1, 1, 2, 2, 2, 1, 5, 2, 4, 2]
def baseStart_3360755 : Nat := 118140960795 + 3360755 * 2 ^ 59
def prefixEnd_3360755 : Nat := 4983230072969 + 3 ^ 40 * 3360755 * 2
def baseEnd_3360755 : Nat := 1725682677001103764306675

theorem tailTrace_3360755 : CollatzResearch.WordTrace tailWord_3360755 prefixEnd_3360755 1725682677001103764306675 := by
  unfold tailWord_3360755
  simp only [CollatzResearch.WordTrace]
  refine ⟨122576804939566081102923719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81717869959710720735282479 122576804939566081102923719)
  ·
    refine ⟨183865207409349121654385579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122576804939566081102923719 183865207409349121654385579)
    ·
      refine ⟨275797811114023682481578369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183865207409349121654385579 275797811114023682481578369)
      ·
        refine ⟨206848358335517761861183777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275797811114023682481578369 206848358335517761861183777)
        ·
          refine ⟨155136268751638321395887833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206848358335517761861183777 155136268751638321395887833)
          ·
            refine ⟨116352201563728741046915875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155136268751638321395887833 116352201563728741046915875)
            ·
              refine ⟨174528302345593111570373813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116352201563728741046915875 174528302345593111570373813)
              ·
                refine ⟨16362028344899354209722545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174528302345593111570373813 16362028344899354209722545)
                ·
                  refine ⟨12271521258674515657291909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16362028344899354209722545 12271521258674515657291909)
                  ·
                    refine ⟨2300910236001471685742233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12271521258674515657291909 2300910236001471685742233)
                    ·
                      refine ⟨1725682677001103764306675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300910236001471685742233 1725682677001103764306675)
                      ·
                        rfl

theorem cell23_3360755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 4, 2].length) (baseStart_3360755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360755 prefixEnd_3360755 := by exact prefixLift 3360755
  have htrace : WordTrace (prefixWord ++ tailWord_3360755) baseStart_3360755 baseEnd_3360755 := by
    simpa [prefixWord, tailWord_3360755, baseEnd_3360755] using wordTrace_append hprefix tailTrace_3360755
  have hstable : (prefixWord ++ tailWord_3360755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360755).length < 2 ^ (prefixWord ++ tailWord_3360755).sum := by decide
  have hdescent : baseEnd_3360755 < baseStart_3360755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360765 : List Nat := [1, 4, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_3360765 : Nat := 118140960795 + 3360765 * 2 ^ 59
def prefixEnd_3360765 : Nat := 4983230072969 + 3 ^ 40 * 3360765 * 2
def baseEnd_3360765 : Nat := 575229270602549575060543

theorem tailTrace_3360765 : CollatzResearch.WordTrace tailWord_3360765 prefixEnd_3360765 575229270602549575060543 := by
  unfold tailWord_3360765
  simp only [CollatzResearch.WordTrace]
  refine ⟨122577169669529852810787749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81718113113019901873858499 122577169669529852810787749)
  ·
    refine ⟨22983219313036847402022703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122577169669529852810787749 22983219313036847402022703)
    ·
      refine ⟨34474828969555271103034055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22983219313036847402022703 34474828969555271103034055)
      ·
        refine ⟨51712243454332906654551083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34474828969555271103034055 51712243454332906654551083)
        ·
          refine ⟨77568365181499359981826625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51712243454332906654551083 77568365181499359981826625)
          ·
            refine ⟨58176273886124519986369969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77568365181499359981826625 58176273886124519986369969)
            ·
              refine ⟨43632205414593389989777477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58176273886124519986369969 43632205414593389989777477)
              ·
                refine ⟨8181038515236260623083277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43632205414593389989777477 8181038515236260623083277)
                ·
                  refine ⟨3067889443213597733656229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8181038515236260623083277 3067889443213597733656229)
                  ·
                    refine ⟨575229270602549575060543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3067889443213597733656229 575229270602549575060543)
                    ·
                      rfl

theorem cell23_3360765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_3360765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360765 prefixEnd_3360765 := by exact prefixLift 3360765
  have htrace : WordTrace (prefixWord ++ tailWord_3360765) baseStart_3360765 baseEnd_3360765 := by
    simpa [prefixWord, tailWord_3360765, baseEnd_3360765] using wordTrace_append hprefix tailTrace_3360765
  have hstable : (prefixWord ++ tailWord_3360765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360765).length < 2 ^ (prefixWord ++ tailWord_3360765).sum := by decide
  have hdescent : baseEnd_3360765 < baseStart_3360765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360832 : List Nat := [2, 1, 1, 2, 2, 5, 1, 1, 1, 5, 2]
def baseStart_3360832 : Nat := 118140960795 + 3360832 * 2 ^ 59
def prefixEnd_3360832 : Nat := 4983230072969 + 3 ^ 40 * 3360832 * 2
def baseEnd_3360832 : Nat := 1725722215011499963043821

theorem tailTrace_3360832 : CollatzResearch.WordTrace tailWord_3360832 prefixEnd_3360832 1725722215011499963043821 := by
  unfold tailWord_3360832
  simp only [CollatzResearch.WordTrace]
  refine ⟨61289806680143561626738375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81719742240191415502317833 61289806680143561626738375)
  ·
    refine ⟨91934710020215342440107563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61289806680143561626738375 91934710020215342440107563)
    ·
      refine ⟨137902065030323013660161345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91934710020215342440107563 137902065030323013660161345)
      ·
        refine ⟨103426548772742260245121009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137902065030323013660161345 103426548772742260245121009)
        ·
          refine ⟨77569911579556695183840757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103426548772742260245121009 77569911579556695183840757)
          ·
            refine ⟨7272179210583440173485071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77569911579556695183840757 7272179210583440173485071)
            ·
              refine ⟨10908268815875160260227607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7272179210583440173485071 10908268815875160260227607)
              ·
                refine ⟨16362403223812740390341411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10908268815875160260227607 16362403223812740390341411)
                ·
                  refine ⟨24543604835719110585512117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16362403223812740390341411 24543604835719110585512117)
                  ·
                    refine ⟨2300962953348666617391761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24543604835719110585512117 2300962953348666617391761)
                    ·
                      refine ⟨1725722215011499963043821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300962953348666617391761 1725722215011499963043821)
                      ·
                        rfl

theorem cell23_3360832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 1, 5, 2].length) (baseStart_3360832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360832 prefixEnd_3360832 := by exact prefixLift 3360832
  have htrace : WordTrace (prefixWord ++ tailWord_3360832) baseStart_3360832 baseEnd_3360832 := by
    simpa [prefixWord, tailWord_3360832, baseEnd_3360832] using wordTrace_append hprefix tailTrace_3360832
  have hstable : (prefixWord ++ tailWord_3360832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360832).length < 2 ^ (prefixWord ++ tailWord_3360832).sum := by decide
  have hdescent : baseEnd_3360832 < baseStart_3360832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360879 : List Nat := [1, 1, 2, 1, 3, 4, 2, 2, 3, 2, 2]
def baseStart_3360879 : Nat := 118140960795 + 3360879 * 2 ^ 59
def prefixEnd_3360879 : Nat := 4983230072969 + 3 ^ 40 * 3360879 * 2
def baseEnd_3360879 : Nat := 1725746348602261279156105

theorem tailTrace_3360879 : CollatzResearch.WordTrace tailWord_3360879 prefixEnd_3360879 1725746348602261279156105 := by
  unfold tailWord_3360879
  simp only [CollatzResearch.WordTrace]
  refine ⟨122581327591116850280437691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81720885060744566853625127 122581327591116850280437691)
  ·
    refine ⟨183871991386675275420656537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122581327591116850280437691 183871991386675275420656537)
    ·
      refine ⟨137903993540006456565492403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183871991386675275420656537 137903993540006456565492403)
      ·
        refine ⟨206855990310009684848238605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137903993540006456565492403 206855990310009684848238605)
        ·
          refine ⟨77570996366253631818089477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206855990310009684848238605 77570996366253631818089477)
          ·
            refine ⟨14544561818672555965891777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77570996366253631818089477 14544561818672555965891777)
            ·
              refine ⟨10908421364004416974418833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14544561818672555965891777 10908421364004416974418833)
              ·
                refine ⟨8181316023003312730814125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10908421364004416974418833 8181316023003312730814125)
                ·
                  refine ⟨3067993508626242274055297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8181316023003312730814125 3067993508626242274055297)
                  ·
                    refine ⟨2300995131469681705541473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3067993508626242274055297 2300995131469681705541473)
                    ·
                      refine ⟨1725746348602261279156105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2300995131469681705541473 1725746348602261279156105)
                      ·
                        rfl

theorem cell23_3360879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 2, 3, 2, 2].length) (baseStart_3360879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360879 prefixEnd_3360879 := by exact prefixLift 3360879
  have htrace : WordTrace (prefixWord ++ tailWord_3360879) baseStart_3360879 baseEnd_3360879 := by
    simpa [prefixWord, tailWord_3360879, baseEnd_3360879] using wordTrace_append hprefix tailTrace_3360879
  have hstable : (prefixWord ++ tailWord_3360879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360879).length < 2 ^ (prefixWord ++ tailWord_3360879).sum := by decide
  have hdescent : baseEnd_3360879 < baseStart_3360879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360912 : List Nat := [2, 1, 1, 1, 1, 1, 5, 3, 4, 1, 3]
def baseStart_3360912 : Nat := 118140960795 + 3360912 * 2 ^ 59
def prefixEnd_3360912 : Nat := 4983230072969 + 3 ^ 40 * 3360912 * 2
def baseEnd_3360912 : Nat := 1725763293463859650043453

theorem tailTrace_3360912 : CollatzResearch.WordTrace tailWord_3360912 prefixEnd_3360912 1725763293463859650043453 := by
  unfold tailWord_3360912
  simp only [CollatzResearch.WordTrace]
  refine ⟨61291265599998648458194495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81721687466664864610925993 61291265599998648458194495)
  ·
    refine ⟨91936898399997972687291743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61291265599998648458194495 91936898399997972687291743)
    ·
      refine ⟨137905347599996959030937615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91936898399997972687291743 137905347599996959030937615)
      ·
        refine ⟨206858021399995438546406423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137905347599996959030937615 206858021399995438546406423)
        ·
          refine ⟨310287032099993157819609635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206858021399995438546406423 310287032099993157819609635)
          ·
            refine ⟨465430548149989736729414453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310287032099993157819609635 465430548149989736729414453)
            ·
              refine ⟨43634113889061537818382605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 465430548149989736729414453 43634113889061537818382605)
              ·
                refine ⟨16362792708398076681893477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43634113889061537818382605 16362792708398076681893477)
                ·
                  refine ⟨3068023632824639377855027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16362792708398076681893477 3068023632824639377855027)
                  ·
                    refine ⟨4602035449236959066782541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3068023632824639377855027 4602035449236959066782541)
                    ·
                      refine ⟨1725763293463859650043453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4602035449236959066782541 1725763293463859650043453)
                      ·
                        rfl

theorem cell23_3360912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 3, 4, 1, 3].length) (baseStart_3360912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360912 prefixEnd_3360912 := by exact prefixLift 3360912
  have htrace : WordTrace (prefixWord ++ tailWord_3360912) baseStart_3360912 baseEnd_3360912 := by
    simpa [prefixWord, tailWord_3360912, baseEnd_3360912] using wordTrace_append hprefix tailTrace_3360912
  have hstable : (prefixWord ++ tailWord_3360912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360912).length < 2 ^ (prefixWord ++ tailWord_3360912).sum := by decide
  have hdescent : baseEnd_3360912 < baseStart_3360912 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360955 : List Nat := [1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 5]
def baseStart_3360955 : Nat := 118140960795 + 3360955 * 2 ^ 59
def prefixEnd_3360955 : Nat := 4983230072969 + 3 ^ 40 * 3360955 * 2
def baseEnd_3360955 : Nat := 1725785373132002981805755

theorem tailTrace_3360955 : CollatzResearch.WordTrace tailWord_3360955 prefixEnd_3360955 1725785373132002981805755 := by
  unfold tailWord_3360955
  simp only [CollatzResearch.WordTrace]
  refine ⟨122584099538841515260204319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81722733025894343506802879 122584099538841515260204319)
  ·
    refine ⟨183876149308262272890306479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122584099538841515260204319 183876149308262272890306479)
    ·
      refine ⟨275814223962393409335459719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183876149308262272890306479 275814223962393409335459719)
      ·
        refine ⟨413721335943590114003189579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275814223962393409335459719 413721335943590114003189579)
        ·
          refine ⟨620582003915385171004784369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413721335943590114003189579 620582003915385171004784369)
          ·
            refine ⟨465436502936538878253588277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620582003915385171004784369 465436502936538878253588277)
            ·
              refine ⟨43634672150300519836273901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 465436502936538878253588277 43634672150300519836273901)
              ·
                refine ⟨16363002056362694938602713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43634672150300519836273901 16363002056362694938602713)
                ·
                  refine ⟨12272251542272021203952035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16363002056362694938602713 12272251542272021203952035)
                  ·
                    refine ⟨18408377313408031805928053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12272251542272021203952035 18408377313408031805928053)
                    ·
                      refine ⟨1725785373132002981805755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18408377313408031805928053 1725785373132002981805755)
                      ·
                        rfl

theorem cell23_3360955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_3360955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360955 prefixEnd_3360955 := by exact prefixLift 3360955
  have htrace : WordTrace (prefixWord ++ tailWord_3360955) baseStart_3360955 baseEnd_3360955 := by
    simpa [prefixWord, tailWord_3360955, baseEnd_3360955] using wordTrace_append hprefix tailTrace_3360955
  have hstable : (prefixWord ++ tailWord_3360955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360955).length < 2 ^ (prefixWord ++ tailWord_3360955).sum := by decide
  have hdescent : baseEnd_3360955 < baseStart_3360955 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360975 : List Nat := [1, 1, 2, 1, 1, 3, 4, 3, 7]
def baseStart_3360975 : Nat := 118140960795 + 3360975 * 2 ^ 59
def prefixEnd_3360975 : Nat := 4983230072969 + 3 ^ 40 * 3360975 * 2
def baseEnd_3360975 : Nat := 191755071416121433728407

theorem tailTrace_3360975 : CollatzResearch.WordTrace tailWord_3360975 prefixEnd_3360975 191755071416121433728407 := by
  unfold tailWord_3360975
  simp only [CollatzResearch.WordTrace]
  refine ⟨122584828998769058675932379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81723219332512705783954919 122584828998769058675932379)
  ·
    refine ⟨183877243498153588013898569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122584828998769058675932379 183877243498153588013898569)
    ·
      refine ⟨137907932623615191010423927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183877243498153588013898569 137907932623615191010423927)
      ·
        refine ⟨206861898935422786515635891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137907932623615191010423927 206861898935422786515635891)
        ·
          refine ⟨310292848403134179773453837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206861898935422786515635891 310292848403134179773453837)
          ·
            refine ⟨116359818151175317415045189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310292848403134179773453837 116359818151175317415045189)
            ·
              refine ⟨21817465903345372015320973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116359818151175317415045189 21817465903345372015320973)
              ·
                refine ⟨8181549713754514505745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21817465903345372015320973 8181549713754514505745365)
                ·
                  refine ⟨191755071416121433728407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8181549713754514505745365 191755071416121433728407)
                  ·
                    rfl

theorem cell23_3360975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 3, 7].length) (baseStart_3360975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360975 prefixEnd_3360975 := by exact prefixLift 3360975
  have htrace : WordTrace (prefixWord ++ tailWord_3360975) baseStart_3360975 baseEnd_3360975 := by
    simpa [prefixWord, tailWord_3360975, baseEnd_3360975] using wordTrace_append hprefix tailTrace_3360975
  have hstable : (prefixWord ++ tailWord_3360975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360975).length < 2 ^ (prefixWord ++ tailWord_3360975).sum := by decide
  have hdescent : baseEnd_3360975 < baseStart_3360975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3360986 : List Nat := [3, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2]
def baseStart_3360986 : Nat := 118140960795 + 3360986 * 2 ^ 59
def prefixEnd_3360986 : Nat := 4983230072969 + 3 ^ 40 * 3360986 * 2
def baseEnd_3360986 : Nat := 1725801291032292360518113

theorem tailTrace_3360986 : CollatzResearch.WordTrace tailWord_3360986 prefixEnd_3360986 1725801291032292360518113 := by
  unfold tailWord_3360986
  simp only [CollatzResearch.WordTrace]
  refine ⟨30646307550432301888645703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81723486801152805036388541 30646307550432301888645703)
  ·
    refine ⟨45969461325648452832968555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30646307550432301888645703 45969461325648452832968555)
    ·
      refine ⟨68954191988472679249452833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45969461325648452832968555 68954191988472679249452833)
      ·
        refine ⟨51715643991354509437089625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68954191988472679249452833 51715643991354509437089625)
        ·
          refine ⟨38786732993515882077817219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51715643991354509437089625 38786732993515882077817219)
          ·
            refine ⟨58180099490273823116725829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38786732993515882077817219 58180099490273823116725829)
            ·
              refine ⟨10908768654426341834386093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58180099490273823116725829 10908768654426341834386093)
              ·
                refine ⟨4090788245409878187894785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10908768654426341834386093 4090788245409878187894785)
                ·
                  refine ⟨3068091184057408640921089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4090788245409878187894785 3068091184057408640921089)
                  ·
                    refine ⟨2301068388043056480690817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3068091184057408640921089 2301068388043056480690817)
                    ·
                      refine ⟨1725801291032292360518113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2301068388043056480690817 1725801291032292360518113)
                      ·
                        rfl

theorem cell23_3360986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_3360986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3360986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3360986 prefixEnd_3360986 := by exact prefixLift 3360986
  have htrace : WordTrace (prefixWord ++ tailWord_3360986) baseStart_3360986 baseEnd_3360986 := by
    simpa [prefixWord, tailWord_3360986, baseEnd_3360986] using wordTrace_append hprefix tailTrace_3360986
  have hstable : (prefixWord ++ tailWord_3360986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3360986).length < 2 ^ (prefixWord ++ tailWord_3360986).sum := by decide
  have hdescent : baseEnd_3360986 < baseStart_3360986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3360986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361002 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_3361002 : Nat := 118140960795 + 3361002 * 2 ^ 59
def prefixEnd_3361002 : Nat := 4983230072969 + 3 ^ 40 * 3361002 * 2
def baseEnd_3361002 : Nat := 1725809506722764297918039

theorem tailTrace_3361002 : CollatzResearch.WordTrace tailWord_3361002 prefixEnd_3361002 1725809506722764297918039 := by
  unfold tailWord_3361002
  simp only [CollatzResearch.WordTrace]
  refine ⟨30646453442417810571791315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81723875846447494858110173 30646453442417810571791315)
  ·
    refine ⟨45969680163626715857686973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30646453442417810571791315 45969680163626715857686973)
    ·
      refine ⟨17238630061360018446632615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45969680163626715857686973 17238630061360018446632615)
      ·
        refine ⟨25857945092040027669948923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17238630061360018446632615 25857945092040027669948923)
        ·
          refine ⟨38786917638060041504923385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25857945092040027669948923 38786917638060041504923385)
          ·
            refine ⟨29090188228545031128692539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38786917638060041504923385 29090188228545031128692539)
            ·
              refine ⟨43635282342817546693038809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29090188228545031128692539 43635282342817546693038809)
              ·
                refine ⟨32726461757113160019779107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43635282342817546693038809 32726461757113160019779107)
                ·
                  refine ⟨49089692635669740029668661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32726461757113160019779107 49089692635669740029668661)
                  ·
                    refine ⟨4602158684594038127781437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49089692635669740029668661 4602158684594038127781437)
                    ·
                      refine ⟨1725809506722764297918039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4602158684594038127781437 1725809506722764297918039)
                      ·
                        rfl

theorem cell23_3361002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_3361002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361002 prefixEnd_3361002 := by exact prefixLift 3361002
  have htrace : WordTrace (prefixWord ++ tailWord_3361002) baseStart_3361002 baseEnd_3361002 := by
    simpa [prefixWord, tailWord_3361002, baseEnd_3361002] using wordTrace_append hprefix tailTrace_3361002
  have hstable : (prefixWord ++ tailWord_3361002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361002).length < 2 ^ (prefixWord ++ tailWord_3361002).sum := by decide
  have hdescent : baseEnd_3361002 < baseStart_3361002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361026 : List Nat := [3, 4, 1, 1, 2, 1, 2, 4, 5]
def baseStart_3361026 : Nat := 118140960795 + 3361026 * 2 ^ 59
def prefixEnd_3361026 : Nat := 4983230072969 + 3 ^ 40 * 3361026 * 2
def baseEnd_3361026 : Nat := 191757981139830244890881

theorem tailTrace_3361026 : CollatzResearch.WordTrace tailWord_3361026 prefixEnd_3361026 191757981139830244890881 := by
  unfold tailWord_3361026
  simp only [CollatzResearch.WordTrace]
  refine ⟨30646672280396073596509733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81724459414389529590692621 30646672280396073596509733)
  ·
    refine ⟨5746251052574263799345575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30646672280396073596509733 5746251052574263799345575)
    ·
      refine ⟨8619376578861395699018363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746251052574263799345575 8619376578861395699018363)
      ·
        refine ⟨12929064868292093548527545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619376578861395699018363 12929064868292093548527545)
        ·
          refine ⟨9696798651219070161395659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12929064868292093548527545 9696798651219070161395659)
          ·
            refine ⟨14545197976828605242093489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9696798651219070161395659 14545197976828605242093489)
            ·
              refine ⟨10908898482621453931570117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14545197976828605242093489 10908898482621453931570117)
              ·
                refine ⟨2045418465491522612169397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10908898482621453931570117 2045418465491522612169397)
                ·
                  refine ⟨191757981139830244890881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2045418465491522612169397 191757981139830244890881)
                  ·
                    rfl

theorem cell23_3361026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_3361026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361026 prefixEnd_3361026 := by exact prefixLift 3361026
  have htrace : WordTrace (prefixWord ++ tailWord_3361026) baseStart_3361026 baseEnd_3361026 := by
    simpa [prefixWord, tailWord_3361026, baseEnd_3361026] using wordTrace_append hprefix tailTrace_3361026
  have hstable : (prefixWord ++ tailWord_3361026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361026).length < 2 ^ (prefixWord ++ tailWord_3361026).sum := by decide
  have hdescent : baseEnd_3361026 < baseStart_3361026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361076 : List Nat := [2, 5, 1, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_3361076 : Nat := 118140960795 + 3361076 * 2 ^ 59
def prefixEnd_3361076 : Nat := 4983230072969 + 3 ^ 40 * 3361076 * 2
def baseEnd_3361076 : Nat := 1725847504291197008392699

theorem tailTrace_3361076 : CollatzResearch.WordTrace tailWord_3361076 prefixEnd_3361076 1725847504291197008392699 := by
  unfold tailWord_3361076
  simp only [CollatzResearch.WordTrace]
  refine ⟨61294256385701576462679541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81725675180935435283572721 61294256385701576462679541)
  ·
    refine ⟨5746336536159522793376207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61294256385701576462679541 5746336536159522793376207)
    ·
      refine ⟨8619504804239284190064311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746336536159522793376207 8619504804239284190064311)
      ·
        refine ⟨12929257206358926285096467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8619504804239284190064311 12929257206358926285096467)
        ·
          refine ⟨19393885809538389427644701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12929257206358926285096467 19393885809538389427644701)
          ·
            refine ⟨7272707178576896035366763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19393885809538389427644701 7272707178576896035366763)
            ·
              refine ⟨10909060767865344053050145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7272707178576896035366763 10909060767865344053050145)
              ·
                refine ⟨8181795575899008039787609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10909060767865344053050145 8181795575899008039787609)
                ·
                  refine ⟨6136346681924256029840707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8181795575899008039787609 6136346681924256029840707)
                  ·
                    refine ⟨9204520022886384044761061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6136346681924256029840707 9204520022886384044761061)
                    ·
                      refine ⟨1725847504291197008392699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9204520022886384044761061 1725847504291197008392699)
                      ·
                        rfl

theorem cell23_3361076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_3361076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361076 prefixEnd_3361076 := by exact prefixLift 3361076
  have htrace : WordTrace (prefixWord ++ tailWord_3361076) baseStart_3361076 baseEnd_3361076 := by
    simpa [prefixWord, tailWord_3361076, baseEnd_3361076] using wordTrace_append hprefix tailTrace_3361076
  have hstable : (prefixWord ++ tailWord_3361076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361076).length < 2 ^ (prefixWord ++ tailWord_3361076).sum := by decide
  have hdescent : baseEnd_3361076 < baseStart_3361076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361082 : List Nat := [3, 1, 1, 1, 4, 2, 2, 1, 8]
def baseStart_3361082 : Nat := 118140960795 + 3361082 * 2 ^ 59
def prefixEnd_3361082 : Nat := 4983230072969 + 3 ^ 40 * 3361082 * 2
def baseEnd_3361082 : Nat := 191761176130569331657519

theorem tailTrace_3361082 : CollatzResearch.WordTrace tailWord_3361082 prefixEnd_3361082 191761176130569331657519 := by
  unfold tailWord_3361082
  simp only [CollatzResearch.WordTrace]
  refine ⟨30647182902345353987519375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81725821072920943966718333 30647182902345353987519375)
  ·
    refine ⟨45970774353518030981279063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30647182902345353987519375 45970774353518030981279063)
    ·
      refine ⟨68956161530277046471918595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45970774353518030981279063 68956161530277046471918595)
      ·
        refine ⟨103434242295415569707877893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68956161530277046471918595 103434242295415569707877893)
        ·
          refine ⟨19393920430390419320227105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103434242295415569707877893 19393920430390419320227105)
          ·
            refine ⟨14545440322792814490170329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19393920430390419320227105 14545440322792814490170329)
            ·
              refine ⟨10909080242094610867627747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14545440322792814490170329 10909080242094610867627747)
              ·
                refine ⟨16363620363141916301441621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10909080242094610867627747 16363620363141916301441621)
                ·
                  refine ⟨191761176130569331657519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16363620363141916301441621 191761176130569331657519)
                  ·
                    rfl

theorem cell23_3361082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_3361082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361082 prefixEnd_3361082 := by exact prefixLift 3361082
  have htrace : WordTrace (prefixWord ++ tailWord_3361082) baseStart_3361082 baseEnd_3361082 := by
    simpa [prefixWord, tailWord_3361082, baseEnd_3361082] using wordTrace_append hprefix tailTrace_3361082
  have hstable : (prefixWord ++ tailWord_3361082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361082).length < 2 ^ (prefixWord ++ tailWord_3361082).sum := by decide
  have hdescent : baseEnd_3361082 < baseStart_3361082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361086 : List Nat := [4, 2, 1, 2, 1, 2, 3, 1, 3, 4]
def baseStart_3361086 : Nat := 118140960795 + 3361086 * 2 ^ 59
def prefixEnd_3361086 : Nat := 4983230072969 + 3 ^ 40 * 3361086 * 2
def baseEnd_3361086 : Nat := 575284213032580656422551

theorem tailTrace_3361086 : CollatzResearch.WordTrace tailWord_3361086 prefixEnd_3361086 575284213032580656422551 := by
  unfold tailWord_3361086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323609687670865579152889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81725918334244616422148741 15323609687670865579152889)
  ·
    refine ⟨11492707265753149184364667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15323609687670865579152889 11492707265753149184364667)
    ·
      refine ⟨17239060898629723776547001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11492707265753149184364667 17239060898629723776547001)
      ·
        refine ⟨12929295673972292832410251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17239060898629723776547001 12929295673972292832410251)
        ·
          refine ⟨19393943510958439248615377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12929295673972292832410251 19393943510958439248615377)
          ·
            refine ⟨14545457633218829436461533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19393943510958439248615377 14545457633218829436461533)
            ·
              refine ⟨5454546612457061038673075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14545457633218829436461533 5454546612457061038673075)
              ·
                refine ⟨8181819918685591558009613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454546612457061038673075 8181819918685591558009613)
                ·
                  refine ⟨3068182469507096834253605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8181819918685591558009613 3068182469507096834253605)
                  ·
                    refine ⟨575284213032580656422551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3068182469507096834253605 575284213032580656422551)
                    ·
                      rfl

theorem cell23_3361086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 1, 3, 4].length) (baseStart_3361086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361086 prefixEnd_3361086 := by exact prefixLift 3361086
  have htrace : WordTrace (prefixWord ++ tailWord_3361086) baseStart_3361086 baseEnd_3361086 := by
    simpa [prefixWord, tailWord_3361086, baseEnd_3361086] using wordTrace_append hprefix tailTrace_3361086
  have hstable : (prefixWord ++ tailWord_3361086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361086).length < 2 ^ (prefixWord ++ tailWord_3361086).sum := by decide
  have hdescent : baseEnd_3361086 < baseStart_3361086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361119 : List Nat := [1, 1, 2, 3, 1, 2, 2, 3, 1, 5, 2]
def baseStart_3361119 : Nat := 118140960795 + 3361119 * 2 ^ 59
def prefixEnd_3361119 : Nat := 4983230072969 + 3 ^ 40 * 3361119 * 2
def baseEnd_3361119 : Nat := 1725869583959340340155001

theorem tailTrace_3361119 : CollatzResearch.WordTrace tailWord_3361119 prefixEnd_3361119 1725869583959340340155001 := by
  unfold tailWord_3361119
  simp only [CollatzResearch.WordTrace]
  refine ⟨122590081110247371269174411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81726720740164914179449607 122590081110247371269174411)
  ·
    refine ⟨183885121665371056903761617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122590081110247371269174411 183885121665371056903761617)
    ·
      refine ⟨137913841249028292677821213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183885121665371056903761617 137913841249028292677821213)
      ·
        refine ⟨51717690468385609754182955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137913841249028292677821213 51717690468385609754182955)
        ·
          refine ⟨77576535702578414631274433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51717690468385609754182955 77576535702578414631274433)
          ·
            refine ⟨58182401776933810973455825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77576535702578414631274433 58182401776933810973455825)
            ·
              refine ⟨43636801332700358230091869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58182401776933810973455825 43636801332700358230091869)
              ·
                refine ⟨16363800499762634336284451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43636801332700358230091869 16363800499762634336284451)
                ·
                  refine ⟨24545700749643951504426677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16363800499762634336284451 24545700749643951504426677)
                  ·
                    refine ⟨2301159445279120453540001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24545700749643951504426677 2301159445279120453540001)
                    ·
                      refine ⟨1725869583959340340155001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2301159445279120453540001 1725869583959340340155001)
                      ·
                        rfl

theorem cell23_3361119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 3, 1, 5, 2].length) (baseStart_3361119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361119 prefixEnd_3361119 := by exact prefixLift 3361119
  have htrace : WordTrace (prefixWord ++ tailWord_3361119) baseStart_3361119 baseEnd_3361119 := by
    simpa [prefixWord, tailWord_3361119, baseEnd_3361119] using wordTrace_append hprefix tailTrace_3361119
  have hstable : (prefixWord ++ tailWord_3361119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361119).length < 2 ^ (prefixWord ++ tailWord_3361119).sum := by decide
  have hdescent : baseEnd_3361119 < baseStart_3361119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361136 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 2, 3, 2]
def baseStart_3361136 : Nat := 118140960795 + 3361136 * 2 ^ 59
def prefixEnd_3361136 : Nat := 4983230072969 + 3 ^ 40 * 3361136 * 2
def baseEnd_3361136 : Nat := 1725878313130466773642423

theorem tailTrace_3361136 : CollatzResearch.WordTrace tailWord_3361136 prefixEnd_3361136 1725878313130466773642423 := by
  unfold tailWord_3361136
  simp only [CollatzResearch.WordTrace]
  refine ⟨61295350575592891586271631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81727134100790522115028841 61295350575592891586271631)
  ·
    refine ⟨91943025863389337379407447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61295350575592891586271631 91943025863389337379407447)
    ·
      refine ⟨137914538795084006069111171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91943025863389337379407447 137914538795084006069111171)
      ·
        refine ⟨206871808192626009103666757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137914538795084006069111171 206871808192626009103666757)
        ·
          refine ⟨38788464036117376706937517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206871808192626009103666757 38788464036117376706937517)
          ·
            refine ⟨14545674013544016265101569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38788464036117376706937517 14545674013544016265101569)
            ·
              refine ⟨10909255510158012198826177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14545674013544016265101569 10909255510158012198826177)
              ·
                refine ⟨8181941632618509149119633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10909255510158012198826177 8181941632618509149119633)
                ·
                  refine ⟨6136456224463881861839725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8181941632618509149119633 6136456224463881861839725)
                  ·
                    refine ⟨2301171084173955698189897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6136456224463881861839725 2301171084173955698189897)
                    ·
                      refine ⟨1725878313130466773642423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2301171084173955698189897 1725878313130466773642423)
                      ·
                        rfl

theorem cell23_3361136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 2, 3, 2].length) (baseStart_3361136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361136 prefixEnd_3361136 := by exact prefixLift 3361136
  have htrace : WordTrace (prefixWord ++ tailWord_3361136) baseStart_3361136 baseEnd_3361136 := by
    simpa [prefixWord, tailWord_3361136, baseEnd_3361136] using wordTrace_append hprefix tailTrace_3361136
  have hstable : (prefixWord ++ tailWord_3361136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361136).length < 2 ^ (prefixWord ++ tailWord_3361136).sum := by decide
  have hdescent : baseEnd_3361136 < baseStart_3361136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361149 : List Nat := [1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_3361149 : Nat := 118140960795 + 3361149 * 2 ^ 59
def prefixEnd_3361149 : Nat := 4983230072969 + 3 ^ 40 * 3361149 * 2
def baseEnd_3361149 : Nat := 1725884988378975222779863

theorem tailTrace_3361149 : CollatzResearch.WordTrace tailWord_3361149 prefixEnd_3361149 1725884988378975222779863 := by
  unfold tailWord_3361149
  simp only [CollatzResearch.WordTrace]
  refine ⟨122591175300138686392766501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81727450200092457595177667 122591175300138686392766501)
  ·
    refine ⟨22985845368776003698643719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122591175300138686392766501 22985845368776003698643719)
    ·
      refine ⟨34478768053164005547965579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22985845368776003698643719 34478768053164005547965579)
      ·
        refine ⟨51718152079746008321948369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34478768053164005547965579 51718152079746008321948369)
        ·
          refine ⟨38788614059809506241461277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51718152079746008321948369 38788614059809506241461277)
          ·
            refine ⟨14545730272428564840547979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38788614059809506241461277 14545730272428564840547979)
            ·
              refine ⟨21818595408642847260821969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14545730272428564840547979 21818595408642847260821969)
              ·
                refine ⟨16363946556482135445616477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21818595408642847260821969 16363946556482135445616477)
                ·
                  refine ⟨6136479958680800792106179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16363946556482135445616477 6136479958680800792106179)
                  ·
                    refine ⟨9204719938021201188159269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6136479958680800792106179 9204719938021201188159269)
                    ·
                      refine ⟨1725884988378975222779863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9204719938021201188159269 1725884988378975222779863)
                      ·
                        rfl

theorem cell23_3361149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_3361149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361149 prefixEnd_3361149 := by exact prefixLift 3361149
  have htrace : WordTrace (prefixWord ++ tailWord_3361149) baseStart_3361149 baseEnd_3361149 := by
    simpa [prefixWord, tailWord_3361149, baseEnd_3361149] using wordTrace_append hprefix tailTrace_3361149
  have hstable : (prefixWord ++ tailWord_3361149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361149).length < 2 ^ (prefixWord ++ tailWord_3361149).sum := by decide
  have hdescent : baseEnd_3361149 < baseStart_3361149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361159 : List Nat := [1, 1, 4, 2, 2, 1, 4, 1, 1, 6]
def baseStart_3361159 : Nat := 118140960795 + 3361159 * 2 ^ 59
def prefixEnd_3361159 : Nat := 4983230072969 + 3 ^ 40 * 3361159 * 2
def baseEnd_3361159 : Nat := 575296707728506727884939

theorem tailTrace_3361159 : CollatzResearch.WordTrace tailWord_3361159 prefixEnd_3361159 575296707728506727884939 := by
  unfold tailWord_3361159
  simp only [CollatzResearch.WordTrace]
  refine ⟨122591540030102458100630531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81727693353401638733753687 122591540030102458100630531)
  ·
    refine ⟨183887310045153687150945797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122591540030102458100630531 183887310045153687150945797)
    ·
      refine ⟨34478870633466316340802337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183887310045153687150945797 34478870633466316340802337)
      ·
        refine ⟨25859152975099737255601753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34478870633466316340802337 25859152975099737255601753)
        ·
          refine ⟨19394364731324802941701315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25859152975099737255601753 19394364731324802941701315)
          ·
            refine ⟨29091547096987204412551973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19394364731324802941701315 29091547096987204412551973)
            ·
              refine ⟨5454665080685100827353495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29091547096987204412551973 5454665080685100827353495)
              ·
                refine ⟨8181997621027651241030243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454665080685100827353495 8181997621027651241030243)
                ·
                  refine ⟨12272996431541476861545365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8181997621027651241030243 12272996431541476861545365)
                  ·
                    refine ⟨575296707728506727884939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12272996431541476861545365 575296707728506727884939)
                    ·
                      rfl

theorem cell23_3361159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 6].length) (baseStart_3361159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361159 prefixEnd_3361159 := by exact prefixLift 3361159
  have htrace : WordTrace (prefixWord ++ tailWord_3361159) baseStart_3361159 baseEnd_3361159 := by
    simpa [prefixWord, tailWord_3361159, baseEnd_3361159] using wordTrace_append hprefix tailTrace_3361159
  have hstable : (prefixWord ++ tailWord_3361159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361159).length < 2 ^ (prefixWord ++ tailWord_3361159).sum := by decide
  have hdescent : baseEnd_3361159 < baseStart_3361159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361166 : List Nat := [4, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3361166 : Nat := 118140960795 + 3361166 * 2 ^ 59
def prefixEnd_3361166 : Nat := 4983230072969 + 3 ^ 40 * 3361166 * 2
def baseEnd_3361166 : Nat := 1725893717550101656267285

theorem tailTrace_3361166 : CollatzResearch.WordTrace tailWord_3361166 prefixEnd_3361166 1725893717550101656267285 := by
  unfold tailWord_3361166
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323974417634637287016919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81727863560718065530756901 15323974417634637287016919)
  ·
    refine ⟨22985961626451955930525379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15323974417634637287016919 22985961626451955930525379)
    ·
      refine ⟨34478942439677933895788069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22985961626451955930525379 34478942439677933895788069)
      ·
        refine ⟨6464801707439612605460263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34478942439677933895788069 6464801707439612605460263)
        ·
          refine ⟨9697202561159418908190395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6464801707439612605460263 9697202561159418908190395)
          ·
            refine ⟨14545803841739128362285593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9697202561159418908190395 14545803841739128362285593)
            ·
              refine ⟨10909352881304346271714195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14545803841739128362285593 10909352881304346271714195)
              ·
                refine ⟨16364029321956519407571293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10909352881304346271714195 16364029321956519407571293)
                ·
                  refine ⟨6136510995733694777839235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16364029321956519407571293 6136510995733694777839235)
                  ·
                    refine ⟨9204766493600542166758853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6136510995733694777839235 9204766493600542166758853)
                    ·
                      refine ⟨1725893717550101656267285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9204766493600542166758853 1725893717550101656267285)
                      ·
                        rfl

theorem cell23_3361166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3361166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361166 prefixEnd_3361166 := by exact prefixLift 3361166
  have htrace : WordTrace (prefixWord ++ tailWord_3361166) baseStart_3361166 baseEnd_3361166 := by
    simpa [prefixWord, tailWord_3361166, baseEnd_3361166] using wordTrace_append hprefix tailTrace_3361166
  have hstable : (prefixWord ++ tailWord_3361166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361166).length < 2 ^ (prefixWord ++ tailWord_3361166).sum := by decide
  have hdescent : baseEnd_3361166 < baseStart_3361166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361217 : List Nat := [1, 2, 7, 1, 1, 1, 2, 2, 1, 1, 4]
def baseStart_3361217 : Nat := 118140960795 + 3361217 * 2 ^ 59
def prefixEnd_3361217 : Nat := 4983230072969 + 3 ^ 40 * 3361217 * 2
def baseEnd_3361217 : Nat := 1725919905063480956729551

theorem tailTrace_3361217 : CollatzResearch.WordTrace tailWord_3361217 prefixEnd_3361217 1725919905063480956729551 := by
  unfold tailWord_3361217
  simp only [CollatzResearch.WordTrace]
  refine ⟨122593655463892334006241905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81729103642594889337494603 122593655463892334006241905)
  ·
    refine ⟨91945241597919250504681429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122593655463892334006241905 91945241597919250504681429)
    ·
      refine ⟨2154966599951232433703471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 91945241597919250504681429 2154966599951232433703471)
      ·
        refine ⟨3232449899926848650555207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2154966599951232433703471 3232449899926848650555207)
        ·
          refine ⟨4848674849890272975832811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232449899926848650555207 4848674849890272975832811)
          ·
            refine ⟨7273012274835409463749217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848674849890272975832811 7273012274835409463749217)
            ·
              refine ⟨5454759206126557097811913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7273012274835409463749217 5454759206126557097811913)
              ·
                refine ⟨4091069404594917823358935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454759206126557097811913 4091069404594917823358935)
                ·
                  refine ⟨6136604106892376735038403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091069404594917823358935 6136604106892376735038403)
                  ·
                    refine ⟨9204906160338565102557605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6136604106892376735038403 9204906160338565102557605)
                    ·
                      refine ⟨1725919905063480956729551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9204906160338565102557605 1725919905063480956729551)
                      ·
                        rfl

theorem cell23_3361217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_3361217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361217 prefixEnd_3361217 := by exact prefixLift 3361217
  have htrace : WordTrace (prefixWord ++ tailWord_3361217) baseStart_3361217 baseEnd_3361217 := by
    simpa [prefixWord, tailWord_3361217, baseEnd_3361217] using wordTrace_append hprefix tailTrace_3361217
  have hstable : (prefixWord ++ tailWord_3361217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361217).length < 2 ^ (prefixWord ++ tailWord_3361217).sum := by decide
  have hdescent : baseEnd_3361217 < baseStart_3361217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361220 : List Nat := [2, 3, 3, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_3361220 : Nat := 118140960795 + 3361220 * 2 ^ 59
def prefixEnd_3361220 : Nat := 4983230072969 + 3 ^ 40 * 3361220 * 2
def baseEnd_3361220 : Nat := 1725921445505444444992037

theorem tailTrace_3361220 : CollatzResearch.WordTrace tailWord_3361220 prefixEnd_3361220 1725921445505444444992037 := by
  unfold tailWord_3361220
  simp only [CollatzResearch.WordTrace]
  refine ⟨61296882441440732759300557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81729176588587643679067409 61296882441440732759300557)
  ·
    refine ⟨22986330915540274784737709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61296882441440732759300557 22986330915540274784737709)
    ·
      refine ⟨8619874093327603044276641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22986330915540274784737709 8619874093327603044276641)
      ·
        refine ⟨6464905569995702283207481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8619874093327603044276641 6464905569995702283207481)
        ·
          refine ⟨4848679177496776712405611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6464905569995702283207481 4848679177496776712405611)
          ·
            refine ⟨7273018766245165068608417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848679177496776712405611 7273018766245165068608417)
            ·
              refine ⟨5454764074683873801456313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7273018766245165068608417 5454764074683873801456313)
              ·
                refine ⟨4091073056012905351092235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5454764074683873801456313 4091073056012905351092235)
                ·
                  refine ⟨6136609584019358026638353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4091073056012905351092235 6136609584019358026638353)
                  ·
                    refine ⟨4602457188014518519978765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6136609584019358026638353 4602457188014518519978765)
                    ·
                      refine ⟨1725921445505444444992037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4602457188014518519978765 1725921445505444444992037)
                      ·
                        rfl

theorem cell23_3361220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_3361220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361220 prefixEnd_3361220 := by exact prefixLift 3361220
  have htrace : WordTrace (prefixWord ++ tailWord_3361220) baseStart_3361220 baseEnd_3361220 := by
    simpa [prefixWord, tailWord_3361220, baseEnd_3361220] using wordTrace_append hprefix tailTrace_3361220
  have hstable : (prefixWord ++ tailWord_3361220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361220).length < 2 ^ (prefixWord ++ tailWord_3361220).sum := by decide
  have hdescent : baseEnd_3361220 < baseStart_3361220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361259 : List Nat := [1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 3]
def baseStart_3361259 : Nat := 118140960795 + 3361259 * 2 ^ 59
def prefixEnd_3361259 : Nat := 4983230072969 + 3 ^ 40 * 3361259 * 2
def baseEnd_3361259 : Nat := 1725941471250969792404357

theorem tailTrace_3361259 : CollatzResearch.WordTrace tailWord_3361259 prefixEnd_3361259 1725941471250969792404357 := by
  unfold tailWord_3361259
  simp only [CollatzResearch.WordTrace]
  refine ⟨122595187329740175179270831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81730124886493450119513887 122595187329740175179270831)
  ·
    refine ⟨183892780994610262768906247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122595187329740175179270831 183892780994610262768906247)
    ·
      refine ⟨275839171491915394153359371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183892780994610262768906247 275839171491915394153359371)
      ·
        refine ⟨413758757237873091230039057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275839171491915394153359371 413758757237873091230039057)
        ·
          refine ⟨310319067928404818422529293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 413758757237873091230039057 310319067928404818422529293)
          ·
            refine ⟨116369650473151806908448485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 310319067928404818422529293 116369650473151806908448485)
            ·
              refine ⟨21819309463715963795334091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116369650473151806908448485 21819309463715963795334091)
              ·
                refine ⟨32728964195573945693001137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21819309463715963795334091 32728964195573945693001137)
                ·
                  refine ⟨24546723146680459269750853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32728964195573945693001137 24546723146680459269750853)
                  ·
                    refine ⟨4602510590002586113078285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24546723146680459269750853 4602510590002586113078285)
                    ·
                      refine ⟨1725941471250969792404357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4602510590002586113078285 1725941471250969792404357)
                      ·
                        rfl

theorem cell23_3361259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 1, 2, 4, 3].length) (baseStart_3361259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361259 prefixEnd_3361259 := by exact prefixLift 3361259
  have htrace : WordTrace (prefixWord ++ tailWord_3361259) baseStart_3361259 baseEnd_3361259 := by
    simpa [prefixWord, tailWord_3361259, baseEnd_3361259] using wordTrace_append hprefix tailTrace_3361259
  have hstable : (prefixWord ++ tailWord_3361259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361259).length < 2 ^ (prefixWord ++ tailWord_3361259).sum := by decide
  have hdescent : baseEnd_3361259 < baseStart_3361259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361289 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 3]
def baseStart_3361289 : Nat := 118140960795 + 3361289 * 2 ^ 59
def prefixEnd_3361289 : Nat := 4983230072969 + 3 ^ 40 * 3361289 * 2
def baseEnd_3361289 : Nat := 1725956875670604675029219

theorem tailTrace_3361289 : CollatzResearch.WordTrace tailWord_3361289 prefixEnd_3361289 1725956875670604675029219 := by
  unfold tailWord_3361289
  simp only [CollatzResearch.WordTrace]
  refine ⟨122596281519631490302862921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81730854346420993535241947 122596281519631490302862921)
  ·
    refine ⟨91947211139723617727147191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122596281519631490302862921 91947211139723617727147191)
    ·
      refine ⟨137920816709585426590720787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91947211139723617727147191 137920816709585426590720787)
      ·
        refine ⟨206881225064378139886081181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137920816709585426590720787 206881225064378139886081181)
        ·
          refine ⟨77580459399141802457280443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206881225064378139886081181 77580459399141802457280443)
          ·
            refine ⟨116370689098712703685920665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77580459399141802457280443 116370689098712703685920665)
            ·
              refine ⟨87278016824034527764440499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116370689098712703685920665 87278016824034527764440499)
              ·
                refine ⟨130917025236051791646660749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87278016824034527764440499 130917025236051791646660749)
                ·
                  refine ⟨49093884463519421867497781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130917025236051791646660749 49093884463519421867497781)
                  ·
                    refine ⟨4602551668454945800077917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49093884463519421867497781 4602551668454945800077917)
                    ·
                      refine ⟨1725956875670604675029219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4602551668454945800077917 1725956875670604675029219)
                      ·
                        rfl

theorem cell23_3361289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 3, 5, 3].length) (baseStart_3361289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361289 prefixEnd_3361289 := by exact prefixLift 3361289
  have htrace : WordTrace (prefixWord ++ tailWord_3361289) baseStart_3361289 baseEnd_3361289 := by
    simpa [prefixWord, tailWord_3361289, baseEnd_3361289] using wordTrace_append hprefix tailTrace_3361289
  have hstable : (prefixWord ++ tailWord_3361289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361289).length < 2 ^ (prefixWord ++ tailWord_3361289).sum := by decide
  have hdescent : baseEnd_3361289 < baseStart_3361289 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361356 : List Nat := [2, 2, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_3361356 : Nat := 118140960795 + 3361356 * 2 ^ 59
def prefixEnd_3361356 : Nat := 4983230072969 + 3 ^ 40 * 3361356 * 2
def baseEnd_3361356 : Nat := 575330426291485304297137

theorem tailTrace_3361356 : CollatzResearch.WordTrace tailWord_3361356 prefixEnd_3361356 575330426291485304297137 := by
  unfold tailWord_3361356
  simp only [CollatzResearch.WordTrace]
  refine ⟨61299362605194380372775961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81732483473592507163701281 61299362605194380372775961)
  ·
    refine ⟨45974521953895785279581971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61299362605194380372775961 45974521953895785279581971)
    ·
      refine ⟨68961782930843677919372957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45974521953895785279581971 68961782930843677919372957)
      ·
        refine ⟨25860668599066379219764859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68961782930843677919372957 25860668599066379219764859)
        ·
          refine ⟨38791002898599568829647289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25860668599066379219764859 38791002898599568829647289)
          ·
            refine ⟨29093252173949676622235467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38791002898599568829647289 29093252173949676622235467)
            ·
              refine ⟨43639878260924514933353201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29093252173949676622235467 43639878260924514933353201)
              ·
                refine ⟨32729908695693386200014901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43639878260924514933353201 32729908695693386200014901)
                ·
                  refine ⟨3068428940221254956251397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32729908695693386200014901 3068428940221254956251397)
                  ·
                    refine ⟨575330426291485304297137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3068428940221254956251397 575330426291485304297137)
                    ·
                      rfl

theorem cell23_3361356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_3361356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361356 prefixEnd_3361356 := by exact prefixLift 3361356
  have htrace : WordTrace (prefixWord ++ tailWord_3361356) baseStart_3361356 baseEnd_3361356 := by
    simpa [prefixWord, tailWord_3361356, baseEnd_3361356] using wordTrace_append hprefix tailTrace_3361356
  have hstable : (prefixWord ++ tailWord_3361356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361356).length < 2 ^ (prefixWord ++ tailWord_3361356).sum := by decide
  have hdescent : baseEnd_3361356 < baseStart_3361356 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361359 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_3361359 : Nat := 118140960795 + 3361359 * 2 ^ 59
def prefixEnd_3361359 : Nat := 4983230072969 + 3 ^ 40 * 3361359 * 2
def baseEnd_3361359 : Nat := 1725992819316419401153897

theorem tailTrace_3361359 : CollatzResearch.WordTrace tailWord_3361359 prefixEnd_3361359 1725992819316419401153897 := by
  unfold tailWord_3361359
  simp only [CollatzResearch.WordTrace]
  refine ⟨122598834629377892257911131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81732556419585261505274087 122598834629377892257911131)
  ·
    refine ⟨183898251944066838386866697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122598834629377892257911131 183898251944066838386866697)
    ·
      refine ⟨137923688958050128790150023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183898251944066838386866697 137923688958050128790150023)
      ·
        refine ⟨206885533437075193185225035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137923688958050128790150023 206885533437075193185225035)
        ·
          refine ⟨310328300155612789777837553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206885533437075193185225035 310328300155612789777837553)
          ·
            refine ⟨232746225116709592333378165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310328300155612789777837553 232746225116709592333378165)
            ·
              refine ⟨21819958604691524281254203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232746225116709592333378165 21819958604691524281254203)
              ·
                refine ⟨32729937907037286421881305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21819958604691524281254203 32729937907037286421881305)
                ·
                  refine ⟨24547453430277964816410979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32729937907037286421881305 24547453430277964816410979)
                  ·
                    refine ⟨36821180145416947224616469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24547453430277964816410979 36821180145416947224616469)
                    ·
                      refine ⟨1725992819316419401153897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36821180145416947224616469 1725992819316419401153897)
                      ·
                        rfl

theorem cell23_3361359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_3361359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361359 prefixEnd_3361359 := by exact prefixLift 3361359
  have htrace : WordTrace (prefixWord ++ tailWord_3361359) baseStart_3361359 baseEnd_3361359 := by
    simpa [prefixWord, tailWord_3361359, baseEnd_3361359] using wordTrace_append hprefix tailTrace_3361359
  have hstable : (prefixWord ++ tailWord_3361359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361359).length < 2 ^ (prefixWord ++ tailWord_3361359).sum := by decide
  have hdescent : baseEnd_3361359 < baseStart_3361359 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361423 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 2, 3, 2]
def baseStart_3361423 : Nat := 118140960795 + 3361423 * 2 ^ 59
def prefixEnd_3361423 : Nat := 4983230072969 + 3 ^ 40 * 3361423 * 2
def baseEnd_3361423 : Nat := 1726025682078307150753603

theorem tailTrace_3361423 : CollatzResearch.WordTrace tailWord_3361423 prefixEnd_3361423 1726025682078307150753603 := by
  unfold tailWord_3361423
  simp only [CollatzResearch.WordTrace]
  refine ⟨122601168901146031188240923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81734112600764020792160615 122601168901146031188240923)
  ·
    refine ⟨183901753351719046782361385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122601168901146031188240923 183901753351719046782361385)
    ·
      refine ⟨137926315013789285086771039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183901753351719046782361385 137926315013789285086771039)
      ·
        refine ⟨206889472520683927630156559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137926315013789285086771039 206889472520683927630156559)
        ·
          refine ⟨310334208781025891445234839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206889472520683927630156559 310334208781025891445234839)
          ·
            refine ⟨465501313171538837167852259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310334208781025891445234839 465501313171538837167852259)
            ·
              refine ⟨698251969757308255751778389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465501313171538837167852259 698251969757308255751778389)
              ·
                refine ⟨8182640270593456122091153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 698251969757308255751778389 8182640270593456122091153)
                ·
                  refine ⟨6136980202945092091568365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8182640270593456122091153 6136980202945092091568365)
                  ·
                    refine ⟨2301367576104409534338137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6136980202945092091568365 2301367576104409534338137)
                    ·
                      refine ⟨1726025682078307150753603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2301367576104409534338137 1726025682078307150753603)
                      ·
                        rfl

theorem cell23_3361423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 2, 3, 2].length) (baseStart_3361423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361423 prefixEnd_3361423 := by exact prefixLift 3361423
  have htrace : WordTrace (prefixWord ++ tailWord_3361423) baseStart_3361423 baseEnd_3361423 := by
    simpa [prefixWord, tailWord_3361423, baseEnd_3361423] using wordTrace_append hprefix tailTrace_3361423
  have hstable : (prefixWord ++ tailWord_3361423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361423).length < 2 ^ (prefixWord ++ tailWord_3361423).sum := by decide
  have hdescent : baseEnd_3361423 < baseStart_3361423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361463 : List Nat := [1, 1, 3, 1, 6, 1, 1, 2, 1, 6]
def baseStart_3361463 : Nat := 118140960795 + 3361463 * 2 ^ 59
def prefixEnd_3361463 : Nat := 4983230072969 + 3 ^ 40 * 3361463 * 2
def baseEnd_3361463 : Nat := 575348740434828998084473

theorem tailTrace_3361463 : CollatzResearch.WordTrace tailWord_3361463 prefixEnd_3361463 575348740434828998084473 := by
  unfold tailWord_3361463
  simp only [CollatzResearch.WordTrace]
  refine ⟨122602627821001118019697043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81735085214000745346464695 122602627821001118019697043)
  ·
    refine ⟨183903941731501677029545565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122602627821001118019697043 183903941731501677029545565)
    ·
      refine ⟨68963978149313128886079587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183903941731501677029545565 68963978149313128886079587)
      ·
        refine ⟨103445967223969693329119381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68963978149313128886079587 103445967223969693329119381)
        ·
          refine ⟨4849029713623579374802471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103445967223969693329119381 4849029713623579374802471)
          ·
            refine ⟨7273544570435369062203707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849029713623579374802471 7273544570435369062203707)
            ·
              refine ⟨10910316855653053593305561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7273544570435369062203707 10910316855653053593305561)
              ·
                refine ⟨8182737641739790194979171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10910316855653053593305561 8182737641739790194979171)
                ·
                  refine ⟨12274106462609685292468757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8182737641739790194979171 12274106462609685292468757)
                  ·
                    refine ⟨575348740434828998084473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12274106462609685292468757 575348740434828998084473)
                    ·
                      rfl

theorem cell23_3361463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_3361463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361463 prefixEnd_3361463 := by exact prefixLift 3361463
  have htrace : WordTrace (prefixWord ++ tailWord_3361463) baseStart_3361463 baseEnd_3361463 := by
    simpa [prefixWord, tailWord_3361463, baseEnd_3361463] using wordTrace_append hprefix tailTrace_3361463
  have hstable : (prefixWord ++ tailWord_3361463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361463).length < 2 ^ (prefixWord ++ tailWord_3361463).sum := by decide
  have hdescent : baseEnd_3361463 < baseStart_3361463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361476 : List Nat := [2, 3, 3, 1, 1, 13]
def baseStart_3361476 : Nat := 118140960795 + 3361476 * 2 ^ 59
def prefixEnd_3361476 : Nat := 4983230072969 + 3 ^ 40 * 3361476 * 2
def baseEnd_3361476 : Nat := 7103098339724261083913

theorem tailTrace_3361476 : CollatzResearch.WordTrace tailWord_3361476 prefixEnd_3361476 7103098339724261083913 := by
  unfold tailWord_3361476
  simp only [CollatzResearch.WordTrace]
  refine ⟨61301550984977010619960141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81735401313302680826613521 61301550984977010619960141)
  ·
    refine ⟨22988081619366378982485053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61301550984977010619960141 22988081619366378982485053)
    ·
      refine ⟨8620530607262392118431895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22988081619366378982485053 8620530607262392118431895)
      ·
        refine ⟨12930795910893588177647843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8620530607262392118431895 12930795910893588177647843)
        ·
          refine ⟨19396193866340382266471765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12930795910893588177647843 19396193866340382266471765)
          ·
            refine ⟨7103098339724261083913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 19396193866340382266471765 7103098339724261083913)
            ·
              rfl

theorem cell23_3361476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 13].length) (baseStart_3361476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361476 prefixEnd_3361476 := by exact prefixLift 3361476
  have htrace : WordTrace (prefixWord ++ tailWord_3361476) baseStart_3361476 baseEnd_3361476 := by
    simpa [prefixWord, tailWord_3361476, baseEnd_3361476] using wordTrace_append hprefix tailTrace_3361476
  have hstable : (prefixWord ++ tailWord_3361476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361476).length < 2 ^ (prefixWord ++ tailWord_3361476).sum := by decide
  have hdescent : baseEnd_3361476 < baseStart_3361476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361480 : List Nat := [2, 1, 3, 1, 2, 4, 2, 2, 2, 4]
def baseStart_3361480 : Nat := 118140960795 + 3361480 * 2 ^ 59
def prefixEnd_3361480 : Nat := 4983230072969 + 3 ^ 40 * 3361480 * 2
def baseEnd_3361480 : Nat := 575351650158537809246947

theorem tailTrace_3361480 : CollatzResearch.WordTrace tailWord_3361480 prefixEnd_3361480 575351650158537809246947 := by
  unfold tailWord_3361480
  simp only [CollatzResearch.WordTrace]
  refine ⟨61301623930969764961532947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81735498574626353282043929 61301623930969764961532947)
  ·
    refine ⟨91952435896454647442299421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61301623930969764961532947 91952435896454647442299421)
    ·
      refine ⟨34482163461170492790862283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91952435896454647442299421 34482163461170492790862283)
      ·
        refine ⟨51723245191755739186293425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34482163461170492790862283 51723245191755739186293425)
        ·
          refine ⟨38792433893816804389720069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51723245191755739186293425 38792433893816804389720069)
          ·
            refine ⟨7273581355090650823072513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38792433893816804389720069 7273581355090650823072513)
            ·
              refine ⟨5455186016317988117304385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7273581355090650823072513 5455186016317988117304385)
              ·
                refine ⟨4091389512238491087978289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5455186016317988117304385 4091389512238491087978289)
                ·
                  refine ⟨3068542134178868315983717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4091389512238491087978289 3068542134178868315983717)
                  ·
                    refine ⟨575351650158537809246947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3068542134178868315983717 575351650158537809246947)
                    ·
                      rfl

theorem cell23_3361480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_3361480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361480 prefixEnd_3361480 := by exact prefixLift 3361480
  have htrace : WordTrace (prefixWord ++ tailWord_3361480) baseStart_3361480 baseEnd_3361480 := by
    simpa [prefixWord, tailWord_3361480, baseEnd_3361480] using wordTrace_append hprefix tailTrace_3361480
  have hstable : (prefixWord ++ tailWord_3361480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361480).length < 2 ^ (prefixWord ++ tailWord_3361480).sum := by decide
  have hdescent : baseEnd_3361480 < baseStart_3361480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361500 : List Nat := [2, 2, 5, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_3361500 : Nat := 118140960795 + 3361500 * 2 ^ 59
def prefixEnd_3361500 : Nat := 4983230072969 + 3 ^ 40 * 3361500 * 2
def baseEnd_3361500 : Nat := 1726065220088703349490749

theorem tailTrace_3361500 : CollatzResearch.WordTrace tailWord_3361500 prefixEnd_3361500 1726065220088703349490749 := by
  unfold tailWord_3361500
  simp only [CollatzResearch.WordTrace]
  refine ⟨61301988660933536669396977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81735984881244715559195969 61301988660933536669396977)
  ·
    refine ⟨45976491495700152502047733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61301988660933536669396977 45976491495700152502047733)
    ·
      refine ⟨4310296077721889297066975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45976491495700152502047733 4310296077721889297066975)
      ·
        refine ⟨6465444116582833945600463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310296077721889297066975 6465444116582833945600463)
        ·
          refine ⟨9698166174874250918400695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465444116582833945600463 9698166174874250918400695)
          ·
            refine ⟨14547249262311376377601043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9698166174874250918400695 14547249262311376377601043)
            ·
              refine ⟨21820873893467064566401565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14547249262311376377601043 21820873893467064566401565)
              ·
                refine ⟨8182827710050149212400587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21820873893467064566401565 8182827710050149212400587)
                ·
                  refine ⟨12274241565075223818600881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8182827710050149212400587 12274241565075223818600881)
                  ·
                    refine ⟨9205681173806417863950661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12274241565075223818600881 9205681173806417863950661)
                    ·
                      refine ⟨1726065220088703349490749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9205681173806417863950661 1726065220088703349490749)
                      ·
                        rfl

theorem cell23_3361500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_3361500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361500 prefixEnd_3361500 := by exact prefixLift 3361500
  have htrace : WordTrace (prefixWord ++ tailWord_3361500) baseStart_3361500 baseEnd_3361500 := by
    simpa [prefixWord, tailWord_3361500, baseEnd_3361500] using wordTrace_append hprefix tailTrace_3361500
  have hstable : (prefixWord ++ tailWord_3361500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361500).length < 2 ^ (prefixWord ++ tailWord_3361500).sum := by decide
  have hdescent : baseEnd_3361500 < baseStart_3361500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361503 : List Nat := [1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 3]
def baseStart_3361503 : Nat := 118140960795 + 3361503 * 2 ^ 59
def prefixEnd_3361503 : Nat := 4983230072969 + 3 ^ 40 * 3361503 * 2
def baseEnd_3361503 : Nat := 1726066760530666837753235

theorem tailTrace_3361503 : CollatzResearch.WordTrace tailWord_3361503 prefixEnd_3361503 1726066760530666837753235 := by
  unfold tailWord_3361503
  simp only [CollatzResearch.WordTrace]
  refine ⟨122604086740856204851153163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81736057827237469900768775 122604086740856204851153163)
  ·
    refine ⟨183906130111284307276729745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122604086740856204851153163 183906130111284307276729745)
    ·
      refine ⟨137929597583463230457547309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183906130111284307276729745 137929597583463230457547309)
      ·
        refine ⟨51723599093798711421580241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137929597583463230457547309 51723599093798711421580241)
        ·
          refine ⟨38792699320349033566185181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51723599093798711421580241 38792699320349033566185181)
          ·
            refine ⟨14547262245130887587319443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38792699320349033566185181 14547262245130887587319443)
            ·
              refine ⟨21820893367696331380979165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14547262245130887587319443 21820893367696331380979165)
              ·
                refine ⟨8182835012886124267867187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21820893367696331380979165 8182835012886124267867187)
                ·
                  refine ⟨12274252519329186401800781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8182835012886124267867187 12274252519329186401800781)
                  ·
                    refine ⟨4602844694748444900675293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12274252519329186401800781 4602844694748444900675293)
                    ·
                      refine ⟨1726066760530666837753235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4602844694748444900675293 1726066760530666837753235)
                      ·
                        rfl

theorem cell23_3361503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 3, 1, 3, 3].length) (baseStart_3361503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361503 prefixEnd_3361503 := by exact prefixLift 3361503
  have htrace : WordTrace (prefixWord ++ tailWord_3361503) baseStart_3361503 baseEnd_3361503 := by
    simpa [prefixWord, tailWord_3361503, baseEnd_3361503] using wordTrace_append hprefix tailTrace_3361503
  have hstable : (prefixWord ++ tailWord_3361503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361503).length < 2 ^ (prefixWord ++ tailWord_3361503).sum := by decide
  have hdescent : baseEnd_3361503 < baseStart_3361503 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361516 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_3361516 : Nat := 118140960795 + 3361516 * 2 ^ 59
def prefixEnd_3361516 : Nat := 4983230072969 + 3 ^ 40 * 3361516 * 2
def baseEnd_3361516 : Nat := 1726073435779175286890675

theorem tailTrace_3361516 : CollatzResearch.WordTrace tailWord_3361516 prefixEnd_3361516 1726073435779175286890675 := by
  unfold tailWord_3361516
  simp only [CollatzResearch.WordTrace]
  refine ⟨61302280444904554035688201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81736373926539405380917601 61302280444904554035688201)
  ·
    refine ⟨45976710333678415526766151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61302280444904554035688201 45976710333678415526766151)
    ·
      refine ⟨68965065500517623290149227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45976710333678415526766151 68965065500517623290149227)
      ·
        refine ⟨103447598250776434935223841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68965065500517623290149227 103447598250776434935223841)
        ·
          refine ⟨77585698688082326201417881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103447598250776434935223841 77585698688082326201417881)
          ·
            refine ⟨58189274016061744651063411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77585698688082326201417881 58189274016061744651063411)
            ·
              refine ⟨87283911024092616976595117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58189274016061744651063411 87283911024092616976595117)
              ·
                refine ⟨32731466634034731366223169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87283911024092616976595117 32731466634034731366223169)
                ·
                  refine ⟨24548599975526048524667377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32731466634034731366223169 24548599975526048524667377)
                  ·
                    refine ⟨18411449981644536393500533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24548599975526048524667377 18411449981644536393500533)
                    ·
                      refine ⟨1726073435779175286890675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18411449981644536393500533 1726073435779175286890675)
                      ·
                        rfl

theorem cell23_3361516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_3361516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361516 prefixEnd_3361516 := by exact prefixLift 3361516
  have htrace : WordTrace (prefixWord ++ tailWord_3361516) baseStart_3361516 baseEnd_3361516 := by
    simpa [prefixWord, tailWord_3361516, baseEnd_3361516] using wordTrace_append hprefix tailTrace_3361516
  have hstable : (prefixWord ++ tailWord_3361516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361516).length < 2 ^ (prefixWord ++ tailWord_3361516).sum := by decide
  have hdescent : baseEnd_3361516 < baseStart_3361516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361554 : List Nat := [3, 2, 4, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_3361554 : Nat := 118140960795 + 3361554 * 2 ^ 59
def prefixEnd_3361554 : Nat := 4983230072969 + 3 ^ 40 * 3361554 * 2
def baseEnd_3361554 : Nat := 1726092948044046138215501

theorem tailTrace_3361554 : CollatzResearch.WordTrace tailWord_3361554 prefixEnd_3361554 1726092948044046138215501 := by
  unfold tailWord_3361554
  simp only [CollatzResearch.WordTrace]
  refine ⟨30651486715917860140314929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81737297909114293707506477 30651486715917860140314929)
  ·
    refine ⟨22988615036938395105236197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30651486715917860140314929 22988615036938395105236197)
    ·
      refine ⟨4310365319425949082231787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22988615036938395105236197 4310365319425949082231787)
      ·
        refine ⟨6465547979138923623347681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310365319425949082231787 6465547979138923623347681)
        ·
          refine ⟨4849160984354192717510761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6465547979138923623347681 4849160984354192717510761)
          ·
            refine ⟨3636870738265644538133071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4849160984354192717510761 3636870738265644538133071)
            ·
              refine ⟨5455306107398466807199607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636870738265644538133071 5455306107398466807199607)
              ·
                refine ⟨8182959161097700210799411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5455306107398466807199607 8182959161097700210799411)
                ·
                  refine ⟨12274438741646550316199117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8182959161097700210799411 12274438741646550316199117)
                  ·
                    refine ⟨4602914528117456368574669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12274438741646550316199117 4602914528117456368574669)
                    ·
                      refine ⟨1726092948044046138215501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4602914528117456368574669 1726092948044046138215501)
                      ·
                        rfl

theorem cell23_3361554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_3361554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361554 prefixEnd_3361554 := by exact prefixLift 3361554
  have htrace : WordTrace (prefixWord ++ tailWord_3361554) baseStart_3361554 baseEnd_3361554 := by
    simpa [prefixWord, tailWord_3361554, baseEnd_3361554] using wordTrace_append hprefix tailTrace_3361554
  have hstable : (prefixWord ++ tailWord_3361554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361554).length < 2 ^ (prefixWord ++ tailWord_3361554).sum := by decide
  have hdescent : baseEnd_3361554 < baseStart_3361554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361650 : List Nat := [3, 2, 1, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3361650 : Nat := 118140960795 + 3361650 * 2 ^ 59
def prefixEnd_3361650 : Nat := 4983230072969 + 3 ^ 40 * 3361650 * 2
def baseEnd_3361650 : Nat := 1726142242186877762615059

theorem tailTrace_3361650 : CollatzResearch.WordTrace tailWord_3361650 prefixEnd_3361650 1726142242186877762615059 := by
  unfold tailWord_3361650
  simp only [CollatzResearch.WordTrace]
  refine ⟨30652362067830912239188601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81739632180882432637836269 30652362067830912239188601)
  ·
    refine ⟨22989271550873184179391451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30652362067830912239188601 22989271550873184179391451)
    ·
      refine ⟨34483907326309776269087177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22989271550873184179391451 34483907326309776269087177)
      ·
        refine ⟨25862930494732332201815383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34483907326309776269087177 25862930494732332201815383)
        ·
          refine ⟨38794395742098498302723075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25862930494732332201815383 38794395742098498302723075)
          ·
            refine ⟨58191593613147747454084613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38794395742098498302723075 58191593613147747454084613)
            ·
              refine ⟨10910923802465202647640865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58191593613147747454084613 10910923802465202647640865)
              ·
                refine ⟨8183192851848901985730649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10910923802465202647640865 8183192851848901985730649)
                ·
                  refine ⟨6137394638886676489297987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8183192851848901985730649 6137394638886676489297987)
                  ·
                    refine ⟨9206091958330014733946981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6137394638886676489297987 9206091958330014733946981)
                    ·
                      refine ⟨1726142242186877762615059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9206091958330014733946981 1726142242186877762615059)
                      ·
                        rfl

theorem cell23_3361650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3361650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361650 prefixEnd_3361650 := by exact prefixLift 3361650
  have htrace : WordTrace (prefixWord ++ tailWord_3361650) baseStart_3361650 baseEnd_3361650 := by
    simpa [prefixWord, tailWord_3361650, baseEnd_3361650] using wordTrace_append hprefix tailTrace_3361650
  have hstable : (prefixWord ++ tailWord_3361650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361650).length < 2 ^ (prefixWord ++ tailWord_3361650).sum := by decide
  have hdescent : baseEnd_3361650 < baseStart_3361650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361683 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 3]
def baseStart_3361683 : Nat := 118140960795 + 3361683 * 2 ^ 59
def prefixEnd_3361683 : Nat := 4983230072969 + 3 ^ 40 * 3361683 * 2
def baseEnd_3361683 : Nat := 1726159187048476133502407

theorem tailTrace_3361683 : CollatzResearch.WordTrace tailWord_3361683 prefixEnd_3361683 1726159187048476133502407 := by
  unfold tailWord_3361683
  simp only [CollatzResearch.WordTrace]
  refine ⟨122610651880204095592705703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81740434586802730395137135 122610651880204095592705703)
  ·
    refine ⟨183915977820306143389058555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122610651880204095592705703 183915977820306143389058555)
    ·
      refine ⟨275873966730459215083587833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183915977820306143389058555 275873966730459215083587833)
      ·
        refine ⟨206905475047844411312690875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275873966730459215083587833 206905475047844411312690875)
        ·
          refine ⟨310358212571766616969036313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206905475047844411312690875 310358212571766616969036313)
          ·
            refine ⟨232768659428824962726777235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310358212571766616969036313 232768659428824962726777235)
            ·
              refine ⟨349152989143237444090165853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232768659428824962726777235 349152989143237444090165853)
              ·
                refine ⟨130932370928714041533812195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349152989143237444090165853 130932370928714041533812195)
                ·
                  refine ⟨196398556393071062300718293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130932370928714041533812195 196398556393071062300718293)
                  ·
                    refine ⟨4603091165462603022673085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 196398556393071062300718293 4603091165462603022673085)
                    ·
                      refine ⟨1726159187048476133502407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4603091165462603022673085 1726159187048476133502407)
                      ·
                        rfl

theorem cell23_3361683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 7, 3].length) (baseStart_3361683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361683 prefixEnd_3361683 := by exact prefixLift 3361683
  have htrace : WordTrace (prefixWord ++ tailWord_3361683) baseStart_3361683 baseEnd_3361683 := by
    simpa [prefixWord, tailWord_3361683, baseEnd_3361683] using wordTrace_append hprefix tailTrace_3361683
  have hstable : (prefixWord ++ tailWord_3361683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361683).length < 2 ^ (prefixWord ++ tailWord_3361683).sum := by decide
  have hdescent : baseEnd_3361683 < baseStart_3361683 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361760 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 3]
def baseStart_3361760 : Nat := 118140960795 + 3361760 * 2 ^ 59
def prefixEnd_3361760 : Nat := 4983230072969 + 3 ^ 40 * 3361760 * 2
def baseEnd_3361760 : Nat := 1726198725058872332239553

theorem tailTrace_3361760 : CollatzResearch.WordTrace tailWord_3361760 prefixEnd_3361760 1726198725058872332239553 := by
  unfold tailWord_3361760
  simp only [CollatzResearch.WordTrace]
  refine ⟨61306730150462568871629367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81742306867283425162172489 61306730150462568871629367)
  ·
    refine ⟨91960095225693853307444051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61306730150462568871629367 91960095225693853307444051)
    ·
      refine ⟨137940142838540779961166077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91960095225693853307444051 137940142838540779961166077)
      ·
        refine ⟨51727553564452792485437279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137940142838540779961166077 51727553564452792485437279)
        ·
          refine ⟨77591330346679188728155919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51727553564452792485437279 77591330346679188728155919)
          ·
            refine ⟨116386995520018783092233879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77591330346679188728155919 116386995520018783092233879)
            ·
              refine ⟨174580493280028174638350819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116386995520018783092233879 174580493280028174638350819)
              ·
                refine ⟨261870739920042261957526229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 174580493280028174638350819 261870739920042261957526229)
                ·
                  refine ⟨6137595466875990514629521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 261870739920042261957526229 6137595466875990514629521)
                  ·
                    refine ⟨4603196600156992885972141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6137595466875990514629521 4603196600156992885972141)
                    ·
                      refine ⟨1726198725058872332239553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4603196600156992885972141 1726198725058872332239553)
                      ·
                        rfl

theorem cell23_3361760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_3361760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361760 prefixEnd_3361760 := by exact prefixLift 3361760
  have htrace : WordTrace (prefixWord ++ tailWord_3361760) baseStart_3361760 baseEnd_3361760 := by
    simpa [prefixWord, tailWord_3361760, baseEnd_3361760] using wordTrace_append hprefix tailTrace_3361760
  have hstable : (prefixWord ++ tailWord_3361760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361760).length < 2 ^ (prefixWord ++ tailWord_3361760).sum := by decide
  have hdescent : baseEnd_3361760 < baseStart_3361760 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361767 : List Nat := [1, 1, 5, 2, 2, 1, 2, 1, 4, 4]
def baseStart_3361767 : Nat := 118140960795 + 3361767 * 2 ^ 59
def prefixEnd_3361767 : Nat := 4983230072969 + 3 ^ 40 * 3361767 * 2
def baseEnd_3361767 : Nat := 575400773141151268284007

theorem tailTrace_3361767 : CollatzResearch.WordTrace tailWord_3361767 prefixEnd_3361767 575400773141151268284007 := by
  unfold tailWord_3361767
  simp only [CollatzResearch.WordTrace]
  refine ⟨122613715611899777938763555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81742477074599851959175703 122613715611899777938763555)
  ·
    refine ⟨183920573417849666908145333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122613715611899777938763555 183920573417849666908145333)
    ·
      refine ⟨17242553757923406272638625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183920573417849666908145333 17242553757923406272638625)
      ·
        refine ⟨12931915318442554704478969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17242553757923406272638625 12931915318442554704478969)
        ·
          refine ⟨9698936488831916028359227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12931915318442554704478969 9698936488831916028359227)
          ·
            refine ⟨14548404733247874042538841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9698936488831916028359227 14548404733247874042538841)
            ·
              refine ⟨10911303549935905531904131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14548404733247874042538841 10911303549935905531904131)
              ·
                refine ⟨16366955324903858297856197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10911303549935905531904131 16366955324903858297856197)
                ·
                  refine ⟨3068804123419473430848037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16366955324903858297856197 3068804123419473430848037)
                  ·
                    refine ⟨575400773141151268284007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3068804123419473430848037 575400773141151268284007)
                    ·
                      rfl

theorem cell23_3361767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_3361767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361767 prefixEnd_3361767 := by exact prefixLift 3361767
  have htrace : WordTrace (prefixWord ++ tailWord_3361767) baseStart_3361767 baseEnd_3361767 := by
    simpa [prefixWord, tailWord_3361767, baseEnd_3361767] using wordTrace_append hprefix tailTrace_3361767
  have hstable : (prefixWord ++ tailWord_3361767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361767).length < 2 ^ (prefixWord ++ tailWord_3361767).sum := by decide
  have hdescent : baseEnd_3361767 < baseStart_3361767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361770 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_3361770 : Nat := 118140960795 + 3361770 * 2 ^ 59
def prefixEnd_3361770 : Nat := 4983230072969 + 3 ^ 40 * 3361770 * 2
def baseEnd_3361770 : Nat := 1726203859865417293114507

theorem tailTrace_3361770 : CollatzResearch.WordTrace tailWord_3361770 prefixEnd_3361770 1726203859865417293114507 := by
  unfold tailWord_3361770
  simp only [CollatzResearch.WordTrace]
  refine ⟨30653456257722227362780691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81742550020592606300748509 30653456257722227362780691)
  ·
    refine ⟨45980184386583341044171037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30653456257722227362780691 45980184386583341044171037)
    ·
      refine ⟨17242569144968752891564139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45980184386583341044171037 17242569144968752891564139)
      ·
        refine ⟨25863853717453129337346209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17242569144968752891564139 25863853717453129337346209)
        ·
          refine ⟨19397890288089847003009657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25863853717453129337346209 19397890288089847003009657)
          ·
            refine ⟨14548417716067385252257243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19397890288089847003009657 14548417716067385252257243)
            ·
              refine ⟨21822626574101077878385865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14548417716067385252257243 21822626574101077878385865)
              ·
                refine ⟨16366969930575808408789399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21822626574101077878385865 16366969930575808408789399)
                ·
                  refine ⟨24550454895863712613184099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16366969930575808408789399 24550454895863712613184099)
                  ·
                    refine ⟨36825682343795568919776149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24550454895863712613184099 36825682343795568919776149)
                    ·
                      refine ⟨1726203859865417293114507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36825682343795568919776149 1726203859865417293114507)
                      ·
                        rfl

theorem cell23_3361770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_3361770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361770 prefixEnd_3361770 := by exact prefixLift 3361770
  have htrace : WordTrace (prefixWord ++ tailWord_3361770) baseStart_3361770 baseEnd_3361770 := by
    simpa [prefixWord, tailWord_3361770, baseEnd_3361770] using wordTrace_append hprefix tailTrace_3361770
  have hstable : (prefixWord ++ tailWord_3361770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361770).length < 2 ^ (prefixWord ++ tailWord_3361770).sum := by decide
  have hdescent : baseEnd_3361770 < baseStart_3361770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361825 : List Nat := [1, 2, 3, 2, 3, 3, 2, 2, 1, 2, 2]
def baseStart_3361825 : Nat := 118140960795 + 3361825 * 2 ^ 59
def prefixEnd_3361825 : Nat := 4983230072969 + 3 ^ 40 * 3361825 * 2
def baseEnd_3361825 : Nat := 1726232101301414577926755

theorem tailTrace_3361825 : CollatzResearch.WordTrace tailWord_3361825 prefixEnd_3361825 1726232101301414577926755 := by
  unfold tailWord_3361825
  simp only [CollatzResearch.WordTrace]
  refine ⟨122615831045689653844374929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81743887363793102562916619 122615831045689653844374929)
  ·
    refine ⟨91961873284267240383281197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122615831045689653844374929 91961873284267240383281197)
    ·
      refine ⟨34485702481600215143730449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91961873284267240383281197 34485702481600215143730449)
      ·
        refine ⟨25864276861200161357797837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34485702481600215143730449 25864276861200161357797837)
        ·
          refine ⟨9699103822950060509174189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25864276861200161357797837 9699103822950060509174189)
          ·
            refine ⟨3637163933606272690940321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9699103822950060509174189 3637163933606272690940321)
            ·
              refine ⟨2727872950204704518205241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3637163933606272690940321 2727872950204704518205241)
              ·
                refine ⟨2045904712653528388653931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2727872950204704518205241 2045904712653528388653931)
                ·
                  refine ⟨3068857068980292582980897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045904712653528388653931 3068857068980292582980897)
                  ·
                    refine ⟨2301642801735219437235673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3068857068980292582980897 2301642801735219437235673)
                    ·
                      refine ⟨1726232101301414577926755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2301642801735219437235673 1726232101301414577926755)
                      ·
                        rfl

theorem cell23_3361825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 2, 2, 1, 2, 2].length) (baseStart_3361825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361825 prefixEnd_3361825 := by exact prefixLift 3361825
  have htrace : WordTrace (prefixWord ++ tailWord_3361825) baseStart_3361825 baseEnd_3361825 := by
    simpa [prefixWord, tailWord_3361825, baseEnd_3361825] using wordTrace_append hprefix tailTrace_3361825
  have hstable : (prefixWord ++ tailWord_3361825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361825).length < 2 ^ (prefixWord ++ tailWord_3361825).sum := by decide
  have hdescent : baseEnd_3361825 < baseStart_3361825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361840 : List Nat := [2, 1, 1, 1, 2, 4, 3, 1, 2, 6]
def baseStart_3361840 : Nat := 118140960795 + 3361840 * 2 ^ 59
def prefixEnd_3361840 : Nat := 4983230072969 + 3 ^ 40 * 3361840 * 2
def baseEnd_3361840 : Nat := 575413267837077339746395

theorem tailTrace_3361840 : CollatzResearch.WordTrace tailWord_3361840 prefixEnd_3361840 575413267837077339746395 := by
  unfold tailWord_3361840
  simp only [CollatzResearch.WordTrace]
  refine ⟨61308189070317655703085487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81744252093756874270780649 61308189070317655703085487)
  ·
    refine ⟨91962283605476483554628231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61308189070317655703085487 91962283605476483554628231)
    ·
      refine ⟨137943425408214725331942347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91962283605476483554628231 137943425408214725331942347)
      ·
        refine ⟨206915138112322087997913521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137943425408214725331942347 206915138112322087997913521)
        ·
          refine ⟨155186353584241565998435141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206915138112322087997913521 155186353584241565998435141)
          ·
            refine ⟨29097441297045293624706589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 155186353584241565998435141 29097441297045293624706589)
            ·
              refine ⟨10911540486391985109264971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29097441297045293624706589 10911540486391985109264971)
              ·
                refine ⟨16367310729587977663897457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10911540486391985109264971 16367310729587977663897457)
                ·
                  refine ⟨12275483047190983247923093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16367310729587977663897457 12275483047190983247923093)
                  ·
                    refine ⟨575413267837077339746395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12275483047190983247923093 575413267837077339746395)
                    ·
                      rfl

theorem cell23_3361840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_3361840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361840 prefixEnd_3361840 := by exact prefixLift 3361840
  have htrace : WordTrace (prefixWord ++ tailWord_3361840) baseStart_3361840 baseEnd_3361840 := by
    simpa [prefixWord, tailWord_3361840, baseEnd_3361840] using wordTrace_append hprefix tailTrace_3361840
  have hstable : (prefixWord ++ tailWord_3361840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361840).length < 2 ^ (prefixWord ++ tailWord_3361840).sum := by decide
  have hdescent : baseEnd_3361840 < baseStart_3361840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361850 : List Nat := [3, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_3361850 : Nat := 118140960795 + 3361850 * 2 ^ 59
def prefixEnd_3361850 : Nat := 4983230072969 + 3 ^ 40 * 3361850 * 2
def baseEnd_3361850 : Nat := 1726244938317776980114139

theorem tailTrace_3361850 : CollatzResearch.WordTrace tailWord_3361850 prefixEnd_3361850 1726244938317776980114139 := by
  unfold tailWord_3361850
  simp only [CollatzResearch.WordTrace]
  refine ⟨30654185717649770778508751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81744495247066055409356669 30654185717649770778508751)
  ·
    refine ⟨45981278576474656167763127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30654185717649770778508751 45981278576474656167763127)
    ·
      refine ⟨68971917864711984251644691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45981278576474656167763127 68971917864711984251644691)
      ·
        refine ⟨103457876797067976377467037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68971917864711984251644691 103457876797067976377467037)
        ·
          refine ⟨38796703798900491141550139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103457876797067976377467037 38796703798900491141550139)
          ·
            refine ⟨58195055698350736712325209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38796703798900491141550139 58195055698350736712325209)
            ·
              refine ⟨43646291773763052534243907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58195055698350736712325209 43646291773763052534243907)
              ·
                refine ⟨65469437660644578801365861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43646291773763052534243907 65469437660644578801365861)
                ·
                  refine ⟨12275519561370858525256099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65469437660644578801365861 12275519561370858525256099)
                  ·
                    refine ⟨18413279342056287787884149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12275519561370858525256099 18413279342056287787884149)
                    ·
                      refine ⟨1726244938317776980114139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18413279342056287787884149 1726244938317776980114139)
                      ·
                        rfl

theorem cell23_3361850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_3361850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361850 prefixEnd_3361850 := by exact prefixLift 3361850
  have htrace : WordTrace (prefixWord ++ tailWord_3361850) baseStart_3361850 baseEnd_3361850 := by
    simpa [prefixWord, tailWord_3361850, baseEnd_3361850] using wordTrace_append hprefix tailTrace_3361850
  have hstable : (prefixWord ++ tailWord_3361850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361850).length < 2 ^ (prefixWord ++ tailWord_3361850).sum := by decide
  have hdescent : baseEnd_3361850 < baseStart_3361850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361864 : List Nat := [2, 1, 3, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_3361864 : Nat := 118140960795 + 3361864 * 2 ^ 59
def prefixEnd_3361864 : Nat := 4983230072969 + 3 ^ 40 * 3361864 * 2
def baseEnd_3361864 : Nat := 1726252127046939925339075

theorem tailTrace_3361864 : CollatzResearch.WordTrace tailWord_3361864 prefixEnd_3361864 1726252127046939925339075 := by
  unfold tailWord_3361864
  simp only [CollatzResearch.WordTrace]
  refine ⟨61308626746274181752522323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81744835661698909003363097 61308626746274181752522323)
  ·
    refine ⟨91962940119411272628783485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61308626746274181752522323 91962940119411272628783485)
    ·
      refine ⟨34486102544779227235793807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91962940119411272628783485 34486102544779227235793807)
      ·
        refine ⟨51729153817168840853690711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34486102544779227235793807 51729153817168840853690711)
        ·
          refine ⟨77593730725753261280536067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51729153817168840853690711 77593730725753261280536067)
          ·
            refine ⟨116390596088629891920804101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77593730725753261280536067 116390596088629891920804101)
            ·
              refine ⟨21823236766618104735150769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116390596088629891920804101 21823236766618104735150769)
              ·
                refine ⟨16367427574963578551363077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21823236766618104735150769 16367427574963578551363077)
                ·
                  refine ⟨3068892670305670978380577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16367427574963578551363077 3068892670305670978380577)
                  ·
                    refine ⟨2301669502729253233785433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3068892670305670978380577 2301669502729253233785433)
                    ·
                      refine ⟨1726252127046939925339075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2301669502729253233785433 1726252127046939925339075)
                      ·
                        rfl

theorem cell23_3361864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_3361864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361864 prefixEnd_3361864 := by exact prefixLift 3361864
  have htrace : WordTrace (prefixWord ++ tailWord_3361864) baseStart_3361864 baseEnd_3361864 := by
    simpa [prefixWord, tailWord_3361864, baseEnd_3361864] using wordTrace_append hprefix tailTrace_3361864
  have hstable : (prefixWord ++ tailWord_3361864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361864).length < 2 ^ (prefixWord ++ tailWord_3361864).sum := by decide
  have hdescent : baseEnd_3361864 < baseStart_3361864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361870 : List Nat := [4, 1, 1, 1, 1, 3, 1, 2, 9]
def baseStart_3361870 : Nat := 118140960795 + 3361870 * 2 ^ 59
def prefixEnd_3361870 : Nat := 4983230072969 + 3 ^ 40 * 3361870 * 2
def baseEnd_3361870 : Nat := 191806134214540766873783

theorem tailTrace_3361870 : CollatzResearch.WordTrace tailWord_3361870 prefixEnd_3361870 191806134214540766873783 := by
  unfold tailWord_3361870
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327184041315828316220383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81744981553684417686508709 15327184041315828316220383)
  ·
    refine ⟨22990776061973742474330575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15327184041315828316220383 22990776061973742474330575)
    ·
      refine ⟨34486164092960613711495863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22990776061973742474330575 34486164092960613711495863)
      ·
        refine ⟨51729246139440920567243795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34486164092960613711495863 51729246139440920567243795)
        ·
          refine ⟨77593869209161380850865693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51729246139440920567243795 77593869209161380850865693)
          ·
            refine ⟨29097700953435517819074635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77593869209161380850865693 29097700953435517819074635)
            ·
              refine ⟨43646551430153276728611953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29097700953435517819074635 43646551430153276728611953)
              ·
                refine ⟨32734913572614957546458965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43646551430153276728611953 32734913572614957546458965)
                ·
                  refine ⟨191806134214540766873783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 32734913572614957546458965 191806134214540766873783)
                  ·
                    rfl

theorem cell23_3361870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 1, 2, 9].length) (baseStart_3361870 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361870 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361870 prefixEnd_3361870 := by exact prefixLift 3361870
  have htrace : WordTrace (prefixWord ++ tailWord_3361870) baseStart_3361870 baseEnd_3361870 := by
    simpa [prefixWord, tailWord_3361870, baseEnd_3361870] using wordTrace_append hprefix tailTrace_3361870
  have hstable : (prefixWord ++ tailWord_3361870).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361870).length < 2 ^ (prefixWord ++ tailWord_3361870).sum := by decide
  have hdescent : baseEnd_3361870 < baseStart_3361870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361887 : List Nat := [1, 1, 2, 3, 1, 1, 3, 6, 5]
def baseStart_3361887 : Nat := 118140960795 + 3361887 * 2 ^ 59
def prefixEnd_3361887 : Nat := 4983230072969 + 3 ^ 40 * 3361887 * 2
def baseEnd_3361887 : Nat := 191807104122443703927941

theorem tailTrace_3361887 : CollatzResearch.WordTrace tailWord_3361887 prefixEnd_3361887 191807104122443703927941 := by
  unfold tailWord_3361887
  simp only [CollatzResearch.WordTrace]
  refine ⟨122618092371465038433131915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81745394914310025622087943 122618092371465038433131915)
  ·
    refine ⟨183927138557197557649697873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122618092371465038433131915 183927138557197557649697873)
    ·
      refine ⟨137945353917898168237273405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183927138557197557649697873 137945353917898168237273405)
      ·
        refine ⟨51729507719211813088977527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137945353917898168237273405 51729507719211813088977527)
        ·
          refine ⟨77594261578817719633466291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51729507719211813088977527 77594261578817719633466291)
          ·
            refine ⟨116391392368226579450199437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77594261578817719633466291 116391392368226579450199437)
            ·
              refine ⟨43646772138084967293824789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116391392368226579450199437 43646772138084967293824789)
              ·
                refine ⟨2045942443972732841898037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43646772138084967293824789 2045942443972732841898037)
                ·
                  refine ⟨191807104122443703927941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2045942443972732841898037 191807104122443703927941)
                  ·
                    rfl

theorem cell23_3361887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 6, 5].length) (baseStart_3361887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361887 prefixEnd_3361887 := by exact prefixLift 3361887
  have htrace : WordTrace (prefixWord ++ tailWord_3361887) baseStart_3361887 baseEnd_3361887 := by
    simpa [prefixWord, tailWord_3361887, baseEnd_3361887] using wordTrace_append hprefix tailTrace_3361887
  have hstable : (prefixWord ++ tailWord_3361887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361887).length < 2 ^ (prefixWord ++ tailWord_3361887).sum := by decide
  have hdescent : baseEnd_3361887 < baseStart_3361887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361897 : List Nat := [1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 3]
def baseStart_3361897 : Nat := 118140960795 + 3361897 * 2 ^ 59
def prefixEnd_3361897 : Nat := 4983230072969 + 3 ^ 40 * 3361897 * 2
def baseEnd_3361897 : Nat := 1726269071908538296226423

theorem tailTrace_3361897 : CollatzResearch.WordTrace tailWord_3361897 prefixEnd_3361897 1726269071908538296226423 := by
  unfold tailWord_3361897
  simp only [CollatzResearch.WordTrace]
  refine ⟨122618457101428810140995945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81745638067619206760663963 122618457101428810140995945)
  ·
    refine ⟨91963842826071607605746959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122618457101428810140995945 91963842826071607605746959)
    ·
      refine ⟨137945764239107411408620439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91963842826071607605746959 137945764239107411408620439)
      ·
        refine ⟨206918646358661117112930659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137945764239107411408620439 206918646358661117112930659)
        ·
          refine ⟨310377969537991675669395989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206918646358661117112930659 310377969537991675669395989)
          ·
            refine ⟨14548967322093359797002937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 310377969537991675669395989 14548967322093359797002937)
            ·
              refine ⟨10911725491570019847752203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14548967322093359797002937 10911725491570019847752203)
              ·
                refine ⟨16367588237355029771628305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10911725491570019847752203 16367588237355029771628305)
                ·
                  refine ⟨12275691178016272328721229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16367588237355029771628305 12275691178016272328721229)
                  ·
                    refine ⟨4603384191756102123270461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12275691178016272328721229 4603384191756102123270461)
                    ·
                      refine ⟨1726269071908538296226423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4603384191756102123270461 1726269071908538296226423)
                      ·
                        rfl

theorem cell23_3361897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 1, 2, 3, 3].length) (baseStart_3361897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361897 prefixEnd_3361897 := by exact prefixLift 3361897
  have htrace : WordTrace (prefixWord ++ tailWord_3361897) baseStart_3361897 baseEnd_3361897 := by
    simpa [prefixWord, tailWord_3361897, baseEnd_3361897] using wordTrace_append hprefix tailTrace_3361897
  have hstable : (prefixWord ++ tailWord_3361897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361897).length < 2 ^ (prefixWord ++ tailWord_3361897).sum := by decide
  have hdescent : baseEnd_3361897 < baseStart_3361897 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361900 : List Nat := [2, 2, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_3361900 : Nat := 118140960795 + 3361900 * 2 ^ 59
def prefixEnd_3361900 : Nat := 4983230072969 + 3 ^ 40 * 3361900 * 2
def baseEnd_3361900 : Nat := 575423537450167261496303

theorem tailTrace_3361900 : CollatzResearch.WordTrace tailWord_3361900 prefixEnd_3361900 575423537450167261496303 := by
  unfold tailWord_3361900
  simp only [CollatzResearch.WordTrace]
  refine ⟨61309283260208970826677577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81745711013611961102236769 61309283260208970826677577)
  ·
    refine ⟨45981962445156728120008183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61309283260208970826677577 45981962445156728120008183)
    ·
      refine ⟨68972943667735092180012275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45981962445156728120008183 68972943667735092180012275)
      ·
        refine ⟨103459415501602638270018413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68972943667735092180012275 103459415501602638270018413)
        ·
          refine ⟨38797280813100989351256905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103459415501602638270018413 38797280813100989351256905)
          ·
            refine ⟨29097960609825742013442679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38797280813100989351256905 29097960609825742013442679)
            ·
              refine ⟨43646940914738613020164019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29097960609825742013442679 43646940914738613020164019)
              ·
                refine ⟨65470411372107919530246029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43646940914738613020164019 65470411372107919530246029)
                ·
                  refine ⟨24551404264540469823842261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65470411372107919530246029 24551404264540469823842261)
                  ·
                    refine ⟨575423537450167261496303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24551404264540469823842261 575423537450167261496303)
                    ·
                      rfl

theorem cell23_3361900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_3361900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361900 prefixEnd_3361900 := by exact prefixLift 3361900
  have htrace : WordTrace (prefixWord ++ tailWord_3361900) baseStart_3361900 baseEnd_3361900 := by
    simpa [prefixWord, tailWord_3361900, baseEnd_3361900] using wordTrace_append hprefix tailTrace_3361900
  have hstable : (prefixWord ++ tailWord_3361900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361900).length < 2 ^ (prefixWord ++ tailWord_3361900).sum := by decide
  have hdescent : baseEnd_3361900 < baseStart_3361900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361917 : List Nat := [1, 4, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_3361917 : Nat := 118140960795 + 3361917 * 2 ^ 59
def prefixEnd_3361917 : Nat := 4983230072969 + 3 ^ 40 * 3361917 * 2
def baseEnd_3361917 : Nat := 575426447173876072658777

theorem tailTrace_3361917 : CollatzResearch.WordTrace tailWord_3361917 prefixEnd_3361917 575426447173876072658777 := by
  unfold tailWord_3361917
  simp only [CollatzResearch.WordTrace]
  refine ⟨122619186561356353556724005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81746124374237569037816003 122619186561356353556724005)
  ·
    refine ⟨22991097480254316291885751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122619186561356353556724005 22991097480254316291885751)
    ·
      refine ⟨34486646220381474437828627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22991097480254316291885751 34486646220381474437828627)
      ·
        refine ⟨51729969330572211656742941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34486646220381474437828627 51729969330572211656742941)
        ·
          refine ⟨19398738498964579371278603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51729969330572211656742941 19398738498964579371278603)
          ·
            refine ⟨29098107748446869056917905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19398738498964579371278603 29098107748446869056917905)
            ·
              refine ⟨21823580811335151792688429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29098107748446869056917905 21823580811335151792688429)
              ·
                refine ⟨8183842804250681922258161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21823580811335151792688429 8183842804250681922258161)
                ·
                  refine ⟨6137882103188011441693621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8183842804250681922258161 6137882103188011441693621)
                  ·
                    refine ⟨575426447173876072658777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6137882103188011441693621 575426447173876072658777)
                    ·
                      rfl

theorem cell23_3361917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_3361917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361917 prefixEnd_3361917 := by exact prefixLift 3361917
  have htrace : WordTrace (prefixWord ++ tailWord_3361917) baseStart_3361917 baseEnd_3361917 := by
    simpa [prefixWord, tailWord_3361917, baseEnd_3361917] using wordTrace_append hprefix tailTrace_3361917
  have hstable : (prefixWord ++ tailWord_3361917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361917).length < 2 ^ (prefixWord ++ tailWord_3361917).sum := by decide
  have hdescent : baseEnd_3361917 < baseStart_3361917 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361918 : List Nat := [4, 2, 4, 1, 1, 1, 1, 1, 2, 1, 5]
def baseStart_3361918 : Nat := 118140960795 + 3361918 * 2 ^ 59
def prefixEnd_3361918 : Nat := 4983230072969 + 3 ^ 40 * 3361918 * 2
def baseEnd_3361918 : Nat := 1726279855002282714063827

theorem tailTrace_3361918 : CollatzResearch.WordTrace tailWord_3361918 prefixEnd_3361918 1726279855002282714063827 := by
  unfold tailWord_3361918
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327402879294091340938801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81746148689568487151673605 15327402879294091340938801)
  ·
    refine ⟨11495552159470568505704101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15327402879294091340938801 11495552159470568505704101)
    ·
      refine ⟨2155416029900731594819519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11495552159470568505704101 2155416029900731594819519)
      ·
        refine ⟨3233124044851097392229279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2155416029900731594819519 3233124044851097392229279)
        ·
          refine ⟨4849686067276646088343919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233124044851097392229279 4849686067276646088343919)
          ·
            refine ⟨7274529100914969132515879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849686067276646088343919 7274529100914969132515879)
            ·
              refine ⟨10911793651372453698773819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7274529100914969132515879 10911793651372453698773819)
              ·
                refine ⟨16367690477058680548160729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10911793651372453698773819 16367690477058680548160729)
                ·
                  refine ⟨12275767857794010411120547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16367690477058680548160729 12275767857794010411120547)
                  ·
                    refine ⟨18413651786691015616680821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12275767857794010411120547 18413651786691015616680821)
                    ·
                      refine ⟨1726279855002282714063827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18413651786691015616680821 1726279855002282714063827)
                      ·
                        rfl

theorem cell23_3361918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_3361918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361918 prefixEnd_3361918 := by exact prefixLift 3361918
  have htrace : WordTrace (prefixWord ++ tailWord_3361918) baseStart_3361918 baseEnd_3361918 := by
    simpa [prefixWord, tailWord_3361918, baseEnd_3361918] using wordTrace_append hprefix tailTrace_3361918
  have hstable : (prefixWord ++ tailWord_3361918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361918).length < 2 ^ (prefixWord ++ tailWord_3361918).sum := by decide
  have hdescent : baseEnd_3361918 < baseStart_3361918 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361921 : List Nat := [1, 2, 4, 2, 2, 3, 1, 3, 5]
def baseStart_3361921 : Nat := 118140960795 + 3361921 * 2 ^ 59
def prefixEnd_3361921 : Nat := 4983230072969 + 3 ^ 40 * 3361921 * 2
def baseEnd_3361921 : Nat := 191809043938249578036257

theorem tailTrace_3361921 : CollatzResearch.WordTrace tailWord_3361921 prefixEnd_3361921 191809043938249578036257 := by
  unfold tailWord_3361921
  simp only [CollatzResearch.WordTrace]
  refine ⟨122619332453341862239869617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81746221635561241493246411 122619332453341862239869617)
  ·
    refine ⟨91964499340006396679902213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122619332453341862239869617 91964499340006396679902213)
    ·
      refine ⟨17243343626251199377481665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91964499340006396679902213 17243343626251199377481665)
      ·
        refine ⟨12932507719688399533111249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17243343626251199377481665 12932507719688399533111249)
        ·
          refine ⟨9699380789766299649833437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12932507719688399533111249 9699380789766299649833437)
          ·
            refine ⟨3637267796162362368687539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9699380789766299649833437 3637267796162362368687539)
            ·
              refine ⟨5455901694243543553031309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3637267796162362368687539 5455901694243543553031309)
              ·
                refine ⟨2045963135341328832386741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5455901694243543553031309 2045963135341328832386741)
                ·
                  refine ⟨191809043938249578036257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2045963135341328832386741 191809043938249578036257)
                  ·
                    rfl

theorem cell23_3361921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 3, 1, 3, 5].length) (baseStart_3361921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361921 prefixEnd_3361921 := by exact prefixLift 3361921
  have htrace : WordTrace (prefixWord ++ tailWord_3361921) baseStart_3361921 baseEnd_3361921 := by
    simpa [prefixWord, tailWord_3361921, baseEnd_3361921] using wordTrace_append hprefix tailTrace_3361921
  have hstable : (prefixWord ++ tailWord_3361921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361921).length < 2 ^ (prefixWord ++ tailWord_3361921).sum := by decide
  have hdescent : baseEnd_3361921 < baseStart_3361921 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361934 : List Nat := [4, 1, 1, 3, 2, 2, 1, 2, 2, 5]
def baseStart_3361934 : Nat := 118140960795 + 3361934 * 2 ^ 59
def prefixEnd_3361934 : Nat := 4983230072969 + 3 ^ 40 * 3361934 * 2
def baseEnd_3361934 : Nat := 575429356897584883821251

theorem tailTrace_3361934 : CollatzResearch.WordTrace tailWord_3361934 prefixEnd_3361934 575429356897584883821251 := by
  unfold tailWord_3361934
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327475825286845682511607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81746537734863176973395237 15327475825286845682511607)
  ·
    refine ⟨22991213737930268523767411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15327475825286845682511607 22991213737930268523767411)
    ·
      refine ⟨34486820606895402785651117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22991213737930268523767411 34486820606895402785651117)
      ·
        refine ⟨12932557727585776044619169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34486820606895402785651117 12932557727585776044619169)
        ·
          refine ⟨9699418295689332033464377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12932557727585776044619169 9699418295689332033464377)
          ·
            refine ⟨7274563721766999025098283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9699418295689332033464377 7274563721766999025098283)
            ·
              refine ⟨10911845582650498537647425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7274563721766999025098283 10911845582650498537647425)
              ·
                refine ⟨8183884186987873903235569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10911845582650498537647425 8183884186987873903235569)
                ·
                  refine ⟨6137913140240905427426677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8183884186987873903235569 6137913140240905427426677)
                  ·
                    refine ⟨575429356897584883821251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6137913140240905427426677 575429356897584883821251)
                    ·
                      rfl

theorem cell23_3361934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_3361934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361934 prefixEnd_3361934 := by exact prefixLift 3361934
  have htrace : WordTrace (prefixWord ++ tailWord_3361934) baseStart_3361934 baseEnd_3361934 := by
    simpa [prefixWord, tailWord_3361934, baseEnd_3361934] using wordTrace_append hprefix tailTrace_3361934
  have hstable : (prefixWord ++ tailWord_3361934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361934).length < 2 ^ (prefixWord ++ tailWord_3361934).sum := by decide
  have hdescent : baseEnd_3361934 < baseStart_3361934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361994 : List Nat := [3, 1, 2, 1, 3, 3, 2, 2, 6]
def baseStart_3361994 : Nat := 118140960795 + 3361994 * 2 ^ 59
def prefixEnd_3361994 : Nat := 4983230072969 + 3 ^ 40 * 3361994 * 2
def baseEnd_3361994 : Nat := 191813208836891601857053

theorem tailTrace_3361994 : CollatzResearch.WordTrace tailWord_3361994 prefixEnd_3361994 191813208836891601857053 := by
  unfold tailWord_3361994
  simp only [CollatzResearch.WordTrace]
  refine ⟨30655498745519348926819259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81747996654718263804851357 30655498745519348926819259)
  ·
    refine ⟨45983248118279023390228889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30655498745519348926819259 45983248118279023390228889)
    ·
      refine ⟨34487436088709267542671667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45983248118279023390228889 34487436088709267542671667)
      ·
        refine ⟨51731154133063901314007501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34487436088709267542671667 51731154133063901314007501)
        ·
          refine ⟨19399182799898962992752813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51731154133063901314007501 19399182799898962992752813)
          ·
            refine ⟨7274693549962111122282305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19399182799898962992752813 7274693549962111122282305)
            ·
              refine ⟨5456020162471583341711729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7274693549962111122282305 5456020162471583341711729)
              ·
                refine ⟨4092015121853687506283797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5456020162471583341711729 4092015121853687506283797)
                ·
                  refine ⟨191813208836891601857053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4092015121853687506283797 191813208836891601857053)
                  ·
                    rfl

theorem cell23_3361994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_3361994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361994 prefixEnd_3361994 := by exact prefixLift 3361994
  have htrace : WordTrace (prefixWord ++ tailWord_3361994) baseStart_3361994 baseEnd_3361994 := by
    simpa [prefixWord, tailWord_3361994, baseEnd_3361994] using wordTrace_append hprefix tailTrace_3361994
  have hstable : (prefixWord ++ tailWord_3361994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361994).length < 2 ^ (prefixWord ++ tailWord_3361994).sum := by decide
  have hdescent : baseEnd_3361994 < baseStart_3361994 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3361998 : List Nat := [4, 1, 1, 1, 5, 1, 1, 4, 1, 4]
def baseStart_3361998 : Nat := 118140960795 + 3361998 * 2 ^ 59
def prefixEnd_3361998 : Nat := 4983230072969 + 3 ^ 40 * 3361998 * 2
def baseEnd_3361998 : Nat := 575440311151547467021153

theorem tailTrace_3361998 : CollatzResearch.WordTrace tailWord_3361998 prefixEnd_3361998 575440311151547467021153 := by
  unfold tailWord_3361998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15327767609257863048802831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81748093916041936260281765 15327767609257863048802831)
  ·
    refine ⟨22991651413886794573204247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15327767609257863048802831 22991651413886794573204247)
    ·
      refine ⟨34487477120830191859806371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22991651413886794573204247 34487477120830191859806371)
      ·
        refine ⟨51731215681245287789709557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34487477120830191859806371 51731215681245287789709557)
        ·
          refine ⟨4849801470116745730285271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51731215681245287789709557 4849801470116745730285271)
          ·
            refine ⟨7274702205175118595427907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849801470116745730285271 7274702205175118595427907)
            ·
              refine ⟨10912053307762677893141861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7274702205175118595427907 10912053307762677893141861)
              ·
                refine ⟨2046009995205502104964099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10912053307762677893141861 2046009995205502104964099)
                ·
                  refine ⟨3069014992808253157446149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046009995205502104964099 3069014992808253157446149)
                  ·
                    refine ⟨575440311151547467021153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069014992808253157446149 575440311151547467021153)
                    ·
                      rfl

theorem cell23_3361998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 4, 1, 4].length) (baseStart_3361998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3361998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3361998 prefixEnd_3361998 := by exact prefixLift 3361998
  have htrace : WordTrace (prefixWord ++ tailWord_3361998) baseStart_3361998 baseEnd_3361998 := by
    simpa [prefixWord, tailWord_3361998, baseEnd_3361998] using wordTrace_append hprefix tailTrace_3361998
  have hstable : (prefixWord ++ tailWord_3361998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3361998).length < 2 ^ (prefixWord ++ tailWord_3361998).sum := by decide
  have hdescent : baseEnd_3361998 < baseStart_3361998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3361998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362007 : List Nat := [1, 1, 3, 2, 1, 2, 3, 2, 3, 5]
def baseStart_3362007 : Nat := 118140960795 + 3362007 * 2 ^ 59
def prefixEnd_3362007 : Nat := 4983230072969 + 3 ^ 40 * 3362007 * 2
def baseEnd_3362007 : Nat := 575441851593510955283639

theorem tailTrace_3362007 : CollatzResearch.WordTrace tailWord_3362007 prefixEnd_3362007 575441851593510955283639 := by
  unfold tailWord_3362007
  simp only [CollatzResearch.WordTrace]
  refine ⟨122622469131030298927500275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81748312754020199285000183 122622469131030298927500275)
  ·
    refine ⟨183933703696545448391250413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122622469131030298927500275 183933703696545448391250413)
    ·
      refine ⟨68975138886204543146718905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183933703696545448391250413 68975138886204543146718905)
      ·
        refine ⟨51731354164653407360039179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68975138886204543146718905 51731354164653407360039179)
        ·
          refine ⟨77597031246980111040058769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51731354164653407360039179 77597031246980111040058769)
          ·
            refine ⟨58197773435235083280044077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77597031246980111040058769 58197773435235083280044077)
            ·
              refine ⟨21824165038213156230016529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58197773435235083280044077 21824165038213156230016529)
              ·
                refine ⟨16368123778659867172512397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21824165038213156230016529 16368123778659867172512397)
                ·
                  refine ⟨6138046416997450189692149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16368123778659867172512397 6138046416997450189692149)
                  ·
                    refine ⟨575441851593510955283639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6138046416997450189692149 575441851593510955283639)
                    ·
                      rfl

theorem cell23_3362007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 5].length) (baseStart_3362007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362007 prefixEnd_3362007 := by exact prefixLift 3362007
  have htrace : WordTrace (prefixWord ++ tailWord_3362007) baseStart_3362007 baseEnd_3362007 := by
    simpa [prefixWord, tailWord_3362007, baseEnd_3362007] using wordTrace_append hprefix tailTrace_3362007
  have hstable : (prefixWord ++ tailWord_3362007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362007).length < 2 ^ (prefixWord ++ tailWord_3362007).sum := by decide
  have hdescent : baseEnd_3362007 < baseStart_3362007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362024 : List Nat := [2, 1, 4, 1, 2, 1, 2, 4, 1, 5]
def baseStart_3362024 : Nat := 118140960795 + 3362024 * 2 ^ 59
def prefixEnd_3362024 : Nat := 4983230072969 + 3 ^ 40 * 3362024 * 2
def baseEnd_3362024 : Nat := 575444761317219766446113

theorem tailTrace_3362024 : CollatzResearch.WordTrace tailWord_3362024 prefixEnd_3362024 575444761317219766446113 := by
  unfold tailWord_3362024
  simp only [CollatzResearch.WordTrace]
  refine ⟨61311544585984355415434563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81748726114645807220579417 61311544585984355415434563)
  ·
    refine ⟨91967316878976533123151845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61311544585984355415434563 91967316878976533123151845)
    ·
      refine ⟨17243871914808099960590971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91967316878976533123151845 17243871914808099960590971)
      ·
        refine ⟨25865807872212149940886457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17243871914808099960590971 25865807872212149940886457)
        ·
          refine ⟨19399355904159112455664843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25865807872212149940886457 19399355904159112455664843)
          ·
            refine ⟨29099033856238668683497265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19399355904159112455664843 29099033856238668683497265)
            ·
              refine ⟨21824275392179001512622949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29099033856238668683497265 21824275392179001512622949)
              ·
                refine ⟨4092051636033562783616803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21824275392179001512622949 4092051636033562783616803)
                ·
                  refine ⟨6138077454050344175425205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092051636033562783616803 6138077454050344175425205)
                  ·
                    refine ⟨575444761317219766446113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6138077454050344175425205 575444761317219766446113)
                    ·
                      rfl

theorem cell23_3362024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_3362024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362024 prefixEnd_3362024 := by exact prefixLift 3362024
  have htrace : WordTrace (prefixWord ++ tailWord_3362024) baseStart_3362024 baseEnd_3362024 := by
    simpa [prefixWord, tailWord_3362024, baseEnd_3362024] using wordTrace_append hprefix tailTrace_3362024
  have hstable : (prefixWord ++ tailWord_3362024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362024).length < 2 ^ (prefixWord ++ tailWord_3362024).sum := by decide
  have hdescent : baseEnd_3362024 < baseStart_3362024 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362031 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 1, 5, 2]
def baseStart_3362031 : Nat := 118140960795 + 3362031 * 2 ^ 59
def prefixEnd_3362031 : Nat := 4983230072969 + 3 ^ 40 * 3362031 * 2
def baseEnd_3362031 : Nat := 1726337878316240771950807

theorem tailTrace_3362031 : CollatzResearch.WordTrace tailWord_3362031 prefixEnd_3362031 1726337878316240771950807 := by
  unfold tailWord_3362031
  simp only [CollatzResearch.WordTrace]
  refine ⟨122623344482943351026373947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81748896321962234017582631 122623344482943351026373947)
  ·
    refine ⟨183935016724415026539560921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122623344482943351026373947 183935016724415026539560921)
    ·
      refine ⟨137951262543311269904670691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183935016724415026539560921 137951262543311269904670691)
      ·
        refine ⟨206926893814966904857006037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137951262543311269904670691 206926893814966904857006037)
        ·
          refine ⟨4849849073788286832586079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 206926893814966904857006037 4849849073788286832586079)
          ·
            refine ⟨7274773610682430248879119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4849849073788286832586079 7274773610682430248879119)
            ·
              refine ⟨10912160416023645373318679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7274773610682430248879119 10912160416023645373318679)
              ·
                refine ⟨16368240624035468059978019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10912160416023645373318679 16368240624035468059978019)
                ·
                  refine ⟨24552360936053202089967029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16368240624035468059978019 24552360936053202089967029)
                  ·
                    refine ⟨2301783837754987695934409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24552360936053202089967029 2301783837754987695934409)
                    ·
                      refine ⟨1726337878316240771950807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2301783837754987695934409 1726337878316240771950807)
                      ·
                        rfl

theorem cell23_3362031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 5, 2].length) (baseStart_3362031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362031 prefixEnd_3362031 := by exact prefixLift 3362031
  have htrace : WordTrace (prefixWord ++ tailWord_3362031) baseStart_3362031 baseEnd_3362031 := by
    simpa [prefixWord, tailWord_3362031, baseEnd_3362031] using wordTrace_append hprefix tailTrace_3362031
  have hstable : (prefixWord ++ tailWord_3362031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362031).length < 2 ^ (prefixWord ++ tailWord_3362031).sum := by decide
  have hdescent : baseEnd_3362031 < baseStart_3362031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362057 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 6]
def baseStart_3362057 : Nat := 118140960795 + 3362057 * 2 ^ 59
def prefixEnd_3362057 : Nat := 4983230072969 + 3 ^ 40 * 3362057 * 2
def baseEnd_3362057 : Nat := 1726351228813257670225687

theorem tailTrace_3362057 : CollatzResearch.WordTrace tailWord_3362057 prefixEnd_3362057 1726351228813257670225687 := by
  unfold tailWord_3362057
  simp only [CollatzResearch.WordTrace]
  refine ⟨122624292780849157466820425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81749528520566104977880283 122624292780849157466820425)
  ·
    refine ⟨91968219585636868100115319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122624292780849157466820425 91968219585636868100115319)
    ·
      refine ⟨137952329378455302150172979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91968219585636868100115319 137952329378455302150172979)
      ·
        refine ⟨206928494067682953225259469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137952329378455302150172979 206928494067682953225259469)
        ·
          refine ⟨77598185275381107459472301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206928494067682953225259469 77598185275381107459472301)
          ·
            refine ⟨29099319478267915297302113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77598185275381107459472301 29099319478267915297302113)
            ·
              refine ⟨21824489608700936472976585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29099319478267915297302113 21824489608700936472976585)
              ·
                refine ⟨16368367206525702354732439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21824489608700936472976585 16368367206525702354732439)
                ·
                  refine ⟨24552550809788553532098659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16368367206525702354732439 24552550809788553532098659)
                  ·
                    refine ⟨36828826214682830298147989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24552550809788553532098659 36828826214682830298147989)
                    ·
                      refine ⟨1726351228813257670225687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36828826214682830298147989 1726351228813257670225687)
                      ·
                        rfl

theorem cell23_3362057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 6].length) (baseStart_3362057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362057 prefixEnd_3362057 := by exact prefixLift 3362057
  have htrace : WordTrace (prefixWord ++ tailWord_3362057) baseStart_3362057 baseEnd_3362057 := by
    simpa [prefixWord, tailWord_3362057, baseEnd_3362057] using wordTrace_append hprefix tailTrace_3362057
  have hstable : (prefixWord ++ tailWord_3362057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362057).length < 2 ^ (prefixWord ++ tailWord_3362057).sum := by decide
  have hdescent : baseEnd_3362057 < baseStart_3362057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362074 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_3362074 : Nat := 118140960795 + 3362074 * 2 ^ 59
def prefixEnd_3362074 : Nat := 4983230072969 + 3 ^ 40 * 3362074 * 2
def baseEnd_3362074 : Nat := 1726359957984384103713109

theorem tailTrace_3362074 : CollatzResearch.WordTrace tailWord_3362074 prefixEnd_3362074 1726359957984384103713109 := by
  unfold tailWord_3362074
  simp only [CollatzResearch.WordTrace]
  refine ⟨30656228205446892342547319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81749941881191712913459517 30656228205446892342547319)
  ·
    refine ⟨45984342308170338513820979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30656228205446892342547319 45984342308170338513820979)
    ·
      refine ⟨68976513462255507770731469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45984342308170338513820979 68976513462255507770731469)
      ·
        refine ⟨25866192548345815414024301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68976513462255507770731469 25866192548345815414024301)
        ·
          refine ⟨9699822205629680780259113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25866192548345815414024301 9699822205629680780259113)
          ·
            refine ⟨7274866654222260585194335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9699822205629680780259113 7274866654222260585194335)
            ·
              refine ⟨10912299981333390877791503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7274866654222260585194335 10912299981333390877791503)
              ·
                refine ⟨16368449972000086316687255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10912299981333390877791503 16368449972000086316687255)
                ·
                  refine ⟨24552674958000129475030883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16368449972000086316687255 24552674958000129475030883)
                  ·
                    refine ⟨36829012437000194212546325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24552674958000129475030883 36829012437000194212546325)
                    ·
                      refine ⟨1726359957984384103713109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36829012437000194212546325 1726359957984384103713109)
                      ·
                        rfl

theorem cell23_3362074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_3362074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362074 prefixEnd_3362074 := by exact prefixLift 3362074
  have htrace : WordTrace (prefixWord ++ tailWord_3362074) baseStart_3362074 baseEnd_3362074 := by
    simpa [prefixWord, tailWord_3362074, baseEnd_3362074] using wordTrace_append hprefix tailTrace_3362074
  have hstable : (prefixWord ++ tailWord_3362074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362074).length < 2 ^ (prefixWord ++ tailWord_3362074).sum := by decide
  have hdescent : baseEnd_3362074 < baseStart_3362074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362111 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 3]
def baseStart_3362111 : Nat := 118140960795 + 3362111 * 2 ^ 59
def prefixEnd_3362111 : Nat := 4983230072969 + 3 ^ 40 * 3362111 * 2
def baseEnd_3362111 : Nat := 1726378956768600458950439

theorem tailTrace_3362111 : CollatzResearch.WordTrace tailWord_3362111 prefixEnd_3362111 1726378956768600458950439 := by
  unfold tailWord_3362111
  simp only [CollatzResearch.WordTrace]
  refine ⟨122626262322653524689286187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81750841548435683126190791 122626262322653524689286187)
  ·
    refine ⟨183939393483980287033929281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122626262322653524689286187 183939393483980287033929281)
    ·
      refine ⟨137954545112985215275446961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183939393483980287033929281 137954545112985215275446961)
      ·
        refine ⟨103465908834738911456585221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137954545112985215275446961 103465908834738911456585221)
        ·
          refine ⟨19399857906513545898109729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103465908834738911456585221 19399857906513545898109729)
          ·
            refine ⟨14549893429885159423582297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19399857906513545898109729 14549893429885159423582297)
            ·
              refine ⟨10912420072413869567686723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14549893429885159423582297 10912420072413869567686723)
              ·
                refine ⟨16368630108620804351530085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10912420072413869567686723 16368630108620804351530085)
                ·
                  refine ⟨3069118145366400815911891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16368630108620804351530085 3069118145366400815911891)
                  ·
                    refine ⟨4603677218049601223867837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3069118145366400815911891 4603677218049601223867837)
                    ·
                      refine ⟨1726378956768600458950439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4603677218049601223867837 1726378956768600458950439)
                      ·
                        rfl

theorem cell23_3362111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 4, 1, 3].length) (baseStart_3362111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362111 prefixEnd_3362111 := by exact prefixLift 3362111
  have htrace : WordTrace (prefixWord ++ tailWord_3362111) baseStart_3362111 baseEnd_3362111 := by
    simpa [prefixWord, tailWord_3362111, baseEnd_3362111] using wordTrace_append hprefix tailTrace_3362111
  have hstable : (prefixWord ++ tailWord_3362111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362111).length < 2 ^ (prefixWord ++ tailWord_3362111).sum := by decide
  have hdescent : baseEnd_3362111 < baseStart_3362111 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362127 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 6, 6]
def baseStart_3362127 : Nat := 118140960795 + 3362127 * 2 ^ 59
def prefixEnd_3362127 : Nat := 4983230072969 + 3 ^ 40 * 3362127 * 2
def baseEnd_3362127 : Nat := 575462390819690798783455

theorem tailTrace_3362127 : CollatzResearch.WordTrace tailWord_3362127 prefixEnd_3362127 575462390819690798783455 := by
  unfold tailWord_3362127
  simp only [CollatzResearch.WordTrace]
  refine ⟨122626845890595559421868635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81751230593730372947912423 122626845890595559421868635)
  ·
    refine ⟨183940268835893339132802953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122626845890595559421868635 183940268835893339132802953)
    ·
      refine ⟨137955201626920004349602215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183940268835893339132802953 137955201626920004349602215)
      ·
        refine ⟨206932802440380006524403323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137955201626920004349602215 206932802440380006524403323)
        ·
          refine ⟨310399203660570009786604985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206932802440380006524403323 310399203660570009786604985)
          ·
            refine ⟨232799402745427507339953739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310399203660570009786604985 232799402745427507339953739)
            ·
              refine ⟨349199104118141261009930609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232799402745427507339953739 349199104118141261009930609)
              ·
                refine ⟨261899328088605945757447957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 349199104118141261009930609 261899328088605945757447957)
                ·
                  refine ⟨12276531004153403707380373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 261899328088605945757447957 12276531004153403707380373)
                  ·
                    refine ⟨575462390819690798783455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12276531004153403707380373 575462390819690798783455)
                    ·
                      rfl

theorem cell23_3362127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_3362127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362127 prefixEnd_3362127 := by exact prefixLift 3362127
  have htrace : WordTrace (prefixWord ++ tailWord_3362127) baseStart_3362127 baseEnd_3362127 := by
    simpa [prefixWord, tailWord_3362127, baseEnd_3362127] using wordTrace_append hprefix tailTrace_3362127
  have hstable : (prefixWord ++ tailWord_3362127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362127).length < 2 ^ (prefixWord ++ tailWord_3362127).sum := by decide
  have hdescent : baseEnd_3362127 < baseStart_3362127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362138 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2]
def baseStart_3362138 : Nat := 118140960795 + 3362138 * 2 ^ 59
def prefixEnd_3362138 : Nat := 4983230072969 + 3 ^ 40 * 3362138 * 2
def baseEnd_3362138 : Nat := 1726392820746271853312815

theorem tailTrace_3362138 : CollatzResearch.WordTrace tailWord_3362138 prefixEnd_3362138 1726392820746271853312815 := by
  unfold tailWord_3362138
  simp only [CollatzResearch.WordTrace]
  refine ⟨30656811773388927075129767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81751498062370472200346045 30656811773388927075129767)
  ·
    refine ⟨45985217660083390612694651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30656811773388927075129767 45985217660083390612694651)
    ·
      refine ⟨68977826490125085919041977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45985217660083390612694651 68977826490125085919041977)
      ·
        refine ⟨51733369867593814439281483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68977826490125085919041977 51733369867593814439281483)
        ·
          refine ⟨77600054801390721658922225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51733369867593814439281483 77600054801390721658922225)
          ·
            refine ⟨58200041101043041244191669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77600054801390721658922225 58200041101043041244191669)
            ·
              refine ⟨5456253853222785116642969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58200041101043041244191669 5456253853222785116642969)
              ·
                refine ⟨4092190389917088837482227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5456253853222785116642969 4092190389917088837482227)
                ·
                  refine ⟨6138285584875633256223341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092190389917088837482227 6138285584875633256223341)
                  ·
                    refine ⟨2301857094328362471083753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6138285584875633256223341 2301857094328362471083753)
                    ·
                      refine ⟨1726392820746271853312815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2301857094328362471083753 1726392820746271853312815)
                      ·
                        rfl

theorem cell23_3362138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_3362138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362138 prefixEnd_3362138 := by exact prefixLift 3362138
  have htrace : WordTrace (prefixWord ++ tailWord_3362138) baseStart_3362138 baseEnd_3362138 := by
    simpa [prefixWord, tailWord_3362138, baseEnd_3362138] using wordTrace_append hprefix tailTrace_3362138
  have hstable : (prefixWord ++ tailWord_3362138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362138).length < 2 ^ (prefixWord ++ tailWord_3362138).sum := by decide
  have hdescent : baseEnd_3362138 < baseStart_3362138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362178 : List Nat := [3, 4, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_3362178 : Nat := 118140960795 + 3362178 * 2 ^ 59
def prefixEnd_3362178 : Nat := 4983230072969 + 3 ^ 40 * 3362178 * 2
def baseEnd_3362178 : Nat := 575471119990817232270877

theorem tailTrace_3362178 : CollatzResearch.WordTrace tailWord_3362178 prefixEnd_3362178 575471119990817232270877 := by
  unfold tailWord_3362178
  simp only [CollatzResearch.WordTrace]
  refine ⟨30657176503352698782993797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81752470675607196754650125 30657176503352698782993797)
  ·
    refine ⟨5748220594378631021811337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30657176503352698782993797 5748220594378631021811337)
    ·
      refine ⟨4311165445783973266358503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5748220594378631021811337 4311165445783973266358503)
      ·
        refine ⟨6466748168675959899537755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311165445783973266358503 6466748168675959899537755)
        ·
          refine ⟨9700122253013939849306633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6466748168675959899537755 9700122253013939849306633)
          ·
            refine ⟨7275091689760454886979975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9700122253013939849306633 7275091689760454886979975)
            ·
              refine ⟨10912637534640682330469963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7275091689760454886979975 10912637534640682330469963)
              ·
                refine ⟨16368956301961023495704945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10912637534640682330469963 16368956301961023495704945)
                ·
                  refine ⟨12276717226470767621778709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16368956301961023495704945 12276717226470767621778709)
                  ·
                    refine ⟨575471119990817232270877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12276717226470767621778709 575471119990817232270877)
                    ·
                      rfl

theorem cell23_3362178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_3362178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362178 prefixEnd_3362178 := by exact prefixLift 3362178
  have htrace : WordTrace (prefixWord ++ tailWord_3362178) baseStart_3362178 baseEnd_3362178 := by
    simpa [prefixWord, tailWord_3362178, baseEnd_3362178] using wordTrace_append hprefix tailTrace_3362178
  have hstable : (prefixWord ++ tailWord_3362178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362178).length < 2 ^ (prefixWord ++ tailWord_3362178).sum := by decide
  have hdescent : baseEnd_3362178 < baseStart_3362178 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362206 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 1, 3, 2]
def baseStart_3362206 : Nat := 118140960795 + 3362206 * 2 ^ 59
def prefixEnd_3362206 : Nat := 4983230072969 + 3 ^ 40 * 3362206 * 2
def baseEnd_3362206 : Nat := 1726427737430777587262503

theorem tailTrace_3362206 : CollatzResearch.WordTrace tailWord_3362206 prefixEnd_3362206 1726427737430777587262503 := by
  unfold tailWord_3362206
  simp only [CollatzResearch.WordTrace]
  refine ⟨15328715907163669489249309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81753151504872903942662981 15328715907163669489249309)
  ·
    refine ⟨5748268465186376058468491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15328715907163669489249309 5748268465186376058468491)
    ·
      refine ⟨8622402697779564087702737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5748268465186376058468491 8622402697779564087702737)
      ·
        refine ⟨6466802023334673065777053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8622402697779564087702737 6466802023334673065777053)
        ·
          refine ⟨2425050758750502399666395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6466802023334673065777053 2425050758750502399666395)
          ·
            refine ⟨3637576138125753599499593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425050758750502399666395 3637576138125753599499593)
            ·
              refine ⟨2728182103594315199624695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3637576138125753599499593 2728182103594315199624695)
              ·
                refine ⟨4092273155391472799437043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728182103594315199624695 4092273155391472799437043)
                ·
                  refine ⟨6138409733087209199155565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092273155391472799437043 6138409733087209199155565)
                  ·
                    refine ⟨2301903649907703449683337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6138409733087209199155565 2301903649907703449683337)
                    ·
                      refine ⟨1726427737430777587262503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2301903649907703449683337 1726427737430777587262503)
                      ·
                        rfl

theorem cell23_3362206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 1, 3, 2].length) (baseStart_3362206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362206 prefixEnd_3362206 := by exact prefixLift 3362206
  have htrace : WordTrace (prefixWord ++ tailWord_3362206) baseStart_3362206 baseEnd_3362206 := by
    simpa [prefixWord, tailWord_3362206, baseEnd_3362206] using wordTrace_append hprefix tailTrace_3362206
  have hstable : (prefixWord ++ tailWord_3362206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362206).length < 2 ^ (prefixWord ++ tailWord_3362206).sum := by decide
  have hdescent : baseEnd_3362206 < baseStart_3362206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362251 : List Nat := [1, 1, 1, 1, 3, 3, 4, 2, 3, 4]
def baseStart_3362251 : Nat := 118140960795 + 3362251 * 2 ^ 59
def prefixEnd_3362251 : Nat := 4983230072969 + 3 ^ 40 * 3362251 * 2
def baseEnd_3362251 : Nat := 575483614686743303733265

theorem tailTrace_3362251 : CollatzResearch.WordTrace tailWord_3362251 prefixEnd_3362251 575483614686743303733265 := by
  unfold tailWord_3362251
  simp only [CollatzResearch.WordTrace]
  refine ⟨122631368542146328599382607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81754245694764219066255071 122631368542146328599382607)
  ·
    refine ⟨183947052813219492899073911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122631368542146328599382607 183947052813219492899073911)
    ·
      refine ⟨275920579219829239348610867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183947052813219492899073911 275920579219829239348610867)
      ·
        refine ⟨413880868829743859022916301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275920579219829239348610867 413880868829743859022916301)
        ·
          refine ⟨155205325811153947133593613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413880868829743859022916301 155205325811153947133593613)
          ·
            refine ⟨58201997179182730175097605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 155205325811153947133593613 58201997179182730175097605)
            ·
              refine ⟨10912874471096761907830801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58201997179182730175097605 10912874471096761907830801)
              ·
                refine ⟨8184655853322571430873101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10912874471096761907830801 8184655853322571430873101)
                ·
                  refine ⟨3069245944995964286577413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8184655853322571430873101 3069245944995964286577413)
                  ·
                    refine ⟨575483614686743303733265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069245944995964286577413 575483614686743303733265)
                    ·
                      rfl

theorem cell23_3362251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 2, 3, 4].length) (baseStart_3362251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362251 prefixEnd_3362251 := by exact prefixLift 3362251
  have htrace : WordTrace (prefixWord ++ tailWord_3362251) baseStart_3362251 baseEnd_3362251 := by
    simpa [prefixWord, tailWord_3362251, baseEnd_3362251] using wordTrace_append hprefix tailTrace_3362251
  have hstable : (prefixWord ++ tailWord_3362251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362251).length < 2 ^ (prefixWord ++ tailWord_3362251).sum := by decide
  have hdescent : baseEnd_3362251 < baseStart_3362251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362261 : List Nat := [1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 3]
def baseStart_3362261 : Nat := 118140960795 + 3362261 * 2 ^ 59
def prefixEnd_3362261 : Nat := 4983230072969 + 3 ^ 40 * 3362261 * 2
def baseEnd_3362261 : Nat := 1726455978866774872074749

theorem tailTrace_3362261 : CollatzResearch.WordTrace tailWord_3362261 prefixEnd_3362261 1726455978866774872074749 := by
  unfold tailWord_3362261
  simp only [CollatzResearch.WordTrace]
  refine ⟨122631733272110100307246637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81754488848073400204831091 122631733272110100307246637)
  ·
    refine ⟨45986899977041287615217489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122631733272110100307246637 45986899977041287615217489)
    ·
      refine ⟨34490174982780965711413117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45986899977041287615217489 34490174982780965711413117)
      ·
        refine ⟨12933815618542862141779919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34490174982780965711413117 12933815618542862141779919)
        ·
          refine ⟨19400723427814293212669879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12933815618542862141779919 19400723427814293212669879)
          ·
            refine ⟨29101085141721439819004819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19400723427814293212669879 29101085141721439819004819)
            ·
              refine ⟨43651627712582159728507229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29101085141721439819004819 43651627712582159728507229)
              ·
                refine ⟨16369360392218309898190211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43651627712582159728507229 16369360392218309898190211)
                ·
                  refine ⟨24554040588327464847285317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16369360392218309898190211 24554040588327464847285317)
                  ·
                    refine ⟨4603882610311399658865997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24554040588327464847285317 4603882610311399658865997)
                    ·
                      refine ⟨1726455978866774872074749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4603882610311399658865997 1726455978866774872074749)
                      ·
                        rfl

theorem cell23_3362261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_3362261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362261 prefixEnd_3362261 := by exact prefixLift 3362261
  have htrace : WordTrace (prefixWord ++ tailWord_3362261) baseStart_3362261 baseEnd_3362261 := by
    simpa [prefixWord, tailWord_3362261, baseEnd_3362261] using wordTrace_append hprefix tailTrace_3362261
  have hstable : (prefixWord ++ tailWord_3362261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362261).length < 2 ^ (prefixWord ++ tailWord_3362261).sum := by decide
  have hdescent : baseEnd_3362261 < baseStart_3362261 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362264 : List Nat := [2, 1, 2, 2, 2, 1, 3, 2, 8]
def baseStart_3362264 : Nat := 118140960795 + 3362264 * 2 ^ 59
def prefixEnd_3362264 : Nat := 4983230072969 + 3 ^ 40 * 3362264 * 2
def baseEnd_3362264 : Nat := 191828613256526484481915

theorem tailTrace_3362264 : CollatzResearch.WordTrace tailWord_3362264 prefixEnd_3362264 191828613256526484481915 := by
  unfold tailWord_3362264
  simp only [CollatzResearch.WordTrace]
  refine ⟨61315921345549615909802923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81754561794066154546403897 61315921345549615909802923)
  ·
    refine ⟨91973882018324423864704385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61315921345549615909802923 91973882018324423864704385)
    ·
      refine ⟨68980411513743317898528289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91973882018324423864704385 68980411513743317898528289)
      ·
        refine ⟨51735308635307488423896217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68980411513743317898528289 51735308635307488423896217)
        ·
          refine ⟨38801481476480616317922163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51735308635307488423896217 38801481476480616317922163)
          ·
            refine ⟨58202222214720924476883245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38801481476480616317922163 58202222214720924476883245)
            ·
              refine ⟨21825833330520346678831217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58202222214720924476883245 21825833330520346678831217)
              ·
                refine ⟨16369374997890260009123413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21825833330520346678831217 16369374997890260009123413)
                ·
                  refine ⟨191828613256526484481915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16369374997890260009123413 191828613256526484481915)
                  ·
                    rfl

theorem cell23_3362264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 3, 2, 8].length) (baseStart_3362264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362264 prefixEnd_3362264 := by exact prefixLift 3362264
  have htrace : WordTrace (prefixWord ++ tailWord_3362264) baseStart_3362264 baseEnd_3362264 := by
    simpa [prefixWord, tailWord_3362264, baseEnd_3362264] using wordTrace_append hprefix tailTrace_3362264
  have hstable : (prefixWord ++ tailWord_3362264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362264).length < 2 ^ (prefixWord ++ tailWord_3362264).sum := by decide
  have hdescent : baseEnd_3362264 < baseStart_3362264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362284 : List Nat := [2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_3362284 : Nat := 118140960795 + 3362284 * 2 ^ 59
def prefixEnd_3362284 : Nat := 4983230072969 + 3 ^ 40 * 3362284 * 2
def baseEnd_3362284 : Nat := 1726467788921828282087143

theorem tailTrace_3362284 : CollatzResearch.WordTrace tailWord_3362284 prefixEnd_3362284 1726467788921828282087143 := by
  unfold tailWord_3362284
  simp only [CollatzResearch.WordTrace]
  refine ⟨61316286075513387617666953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81755048100684516823555937 61316286075513387617666953)
  ·
    refine ⟨45987214556635040713250215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61316286075513387617666953 45987214556635040713250215)
    ·
      refine ⟨68980821834952561069875323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45987214556635040713250215 68980821834952561069875323)
      ·
        refine ⟨103471232752428841604812985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68980821834952561069875323 103471232752428841604812985)
        ·
          refine ⟨77603424564321631203609739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103471232752428841604812985 77603424564321631203609739)
          ·
            refine ⟨116405136846482446805414609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77603424564321631203609739 116405136846482446805414609)
            ·
              refine ⟨87303852634861835104060957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116405136846482446805414609 87303852634861835104060957)
              ·
                refine ⟨32738944738073188164022859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87303852634861835104060957 32738944738073188164022859)
                ·
                  refine ⟨49108417107109782246034289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32738944738073188164022859 49108417107109782246034289)
                  ·
                    refine ⟨36831312830332336684525717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49108417107109782246034289 36831312830332336684525717)
                    ·
                      refine ⟨1726467788921828282087143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36831312830332336684525717 1726467788921828282087143)
                      ·
                        rfl

theorem cell23_3362284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_3362284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362284 prefixEnd_3362284 := by exact prefixLift 3362284
  have htrace : WordTrace (prefixWord ++ tailWord_3362284) baseStart_3362284 baseEnd_3362284 := by
    simpa [prefixWord, tailWord_3362284, baseEnd_3362284] using wordTrace_append hprefix tailTrace_3362284
  have hstable : (prefixWord ++ tailWord_3362284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362284).length < 2 ^ (prefixWord ++ tailWord_3362284).sum := by decide
  have hdescent : baseEnd_3362284 < baseStart_3362284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362368 : List Nat := [2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 3]
def baseStart_3362368 : Nat := 118140960795 + 3362368 * 2 ^ 59
def prefixEnd_3362368 : Nat := 4983230072969 + 3 ^ 40 * 3362368 * 2
def baseEnd_3362368 : Nat := 1726510921296805953436757

theorem tailTrace_3362368 : CollatzResearch.WordTrace tailWord_3362368 prefixEnd_3362368 1726510921296805953436757 := by
  unfold tailWord_3362368
  simp only [CollatzResearch.WordTrace]
  refine ⟨61317817941361228790695879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81757090588481638387594505 61317817941361228790695879)
  ·
    refine ⟨91976726912041843186043819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61317817941361228790695879 91976726912041843186043819)
    ·
      refine ⟨137965090368062764779065729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91976726912041843186043819 137965090368062764779065729)
      ·
        refine ⟨103473817776047073584299297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137965090368062764779065729 103473817776047073584299297)
        ·
          refine ⟨77605363332035305188224473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103473817776047073584299297 77605363332035305188224473)
          ·
            refine ⟨58204022499026478891168355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77605363332035305188224473 58204022499026478891168355)
            ·
              refine ⟨87306033748539718336752533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58204022499026478891168355 87306033748539718336752533)
              ·
                refine ⟨4092470331962799297035275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87306033748539718336752533 4092470331962799297035275)
                ·
                  refine ⟨6138705497944198945552913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092470331962799297035275 6138705497944198945552913)
                  ·
                    refine ⟨4604029123458149209164685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6138705497944198945552913 4604029123458149209164685)
                    ·
                      refine ⟨1726510921296805953436757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4604029123458149209164685 1726510921296805953436757)
                      ·
                        rfl

theorem cell23_3362368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_3362368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362368 prefixEnd_3362368 := by exact prefixLift 3362368
  have htrace : WordTrace (prefixWord ++ tailWord_3362368) baseStart_3362368 baseEnd_3362368 := by
    simpa [prefixWord, tailWord_3362368, baseEnd_3362368] using wordTrace_append hprefix tailTrace_3362368
  have hstable : (prefixWord ++ tailWord_3362368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362368).length < 2 ^ (prefixWord ++ tailWord_3362368).sum := by decide
  have hdescent : baseEnd_3362368 < baseStart_3362368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362441 : List Nat := [1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 5]
def baseStart_3362441 : Nat := 118140960795 + 3362441 * 2 ^ 59
def prefixEnd_3362441 : Nat := 4983230072969 + 3 ^ 40 * 3362441 * 2
def baseEnd_3362441 : Nat := 1726548405384584167823921

theorem tailTrace_3362441 : CollatzResearch.WordTrace tailWord_3362441 prefixEnd_3362441 1726548405384584167823921 := by
  unfold tailWord_3362441
  simp only [CollatzResearch.WordTrace]
  refine ⟨122638298411457991048799177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81758865607638660699199451 122638298411457991048799177)
  ·
    refine ⟨91978723808593493286599383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122638298411457991048799177 91978723808593493286599383)
    ·
      refine ⟨137968085712890239929899075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91978723808593493286599383 137968085712890239929899075)
      ·
        refine ⟨206952128569335359894848613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137968085712890239929899075 206952128569335359894848613)
        ·
          refine ⟨38803524106750379980284115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206952128569335359894848613 38803524106750379980284115)
          ·
            refine ⟨58205286160125569970426173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38803524106750379980284115 58205286160125569970426173)
            ·
              refine ⟨21826982310047088738909815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58205286160125569970426173 21826982310047088738909815)
              ·
                refine ⟨32740473465070633108364723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21826982310047088738909815 32740473465070633108364723)
                ·
                  refine ⟨49110710197605949662547085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32740473465070633108364723 49110710197605949662547085)
                  ·
                    refine ⟨18416516324102231123455157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49110710197605949662547085 18416516324102231123455157)
                    ·
                      refine ⟨1726548405384584167823921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18416516324102231123455157 1726548405384584167823921)
                      ·
                        rfl

theorem cell23_3362441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 3, 5].length) (baseStart_3362441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362441 prefixEnd_3362441 := by exact prefixLift 3362441
  have htrace : WordTrace (prefixWord ++ tailWord_3362441) baseStart_3362441 baseEnd_3362441 := by
    simpa [prefixWord, tailWord_3362441, baseEnd_3362441] using wordTrace_append hprefix tailTrace_3362441
  have hstable : (prefixWord ++ tailWord_3362441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362441).length < 2 ^ (prefixWord ++ tailWord_3362441).sum := by decide
  have hdescent : baseEnd_3362441 < baseStart_3362441 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362442 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_3362442 : Nat := 118140960795 + 3362442 * 2 ^ 59
def prefixEnd_3362442 : Nat := 4983230072969 + 3 ^ 40 * 3362442 * 2
def baseEnd_3362442 : Nat := 1726548918865238663911417

theorem tailTrace_3362442 : CollatzResearch.WordTrace tailWord_3362442 prefixEnd_3362442 1726548918865238663911417 := by
  unfold tailWord_3362442
  simp only [CollatzResearch.WordTrace]
  refine ⟨30659583721113592054896395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81758889922969578813057053 30659583721113592054896395)
  ·
    refine ⟨45989375581670388082344593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30659583721113592054896395 45989375581670388082344593)
    ·
      refine ⟨34492031686252791061758445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45989375581670388082344593 34492031686252791061758445)
      ·
        refine ⟨12934511882344796648159417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34492031686252791061758445 12934511882344796648159417)
        ·
          refine ⟨9700883911758597486119563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12934511882344796648159417 9700883911758597486119563)
          ·
            refine ⟨14551325867637896229179345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9700883911758597486119563 14551325867637896229179345)
            ·
              refine ⟨10913494400728422171884509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14551325867637896229179345 10913494400728422171884509)
              ·
                refine ⟨4092560400273158314456691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10913494400728422171884509 4092560400273158314456691)
                ·
                  refine ⟨6138840600409737471685037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092560400273158314456691 6138840600409737471685037)
                  ·
                    refine ⟨2302065225153651551881889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6138840600409737471685037 2302065225153651551881889)
                    ·
                      refine ⟨1726548918865238663911417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2302065225153651551881889 1726548918865238663911417)
                      ·
                        rfl

theorem cell23_3362442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_3362442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362442 prefixEnd_3362442 := by exact prefixLift 3362442
  have htrace : WordTrace (prefixWord ++ tailWord_3362442) baseStart_3362442 baseEnd_3362442 := by
    simpa [prefixWord, tailWord_3362442, baseEnd_3362442] using wordTrace_append hprefix tailTrace_3362442
  have hstable : (prefixWord ++ tailWord_3362442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362442).length < 2 ^ (prefixWord ++ tailWord_3362442).sum := by decide
  have hdescent : baseEnd_3362442 < baseStart_3362442 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362491 : List Nat := [1, 1, 1, 1, 1, 2, 3, 5, 1, 7]
def baseStart_3362491 : Nat := 118140960795 + 3362491 * 2 ^ 59
def prefixEnd_3362491 : Nat := 4983230072969 + 3 ^ 40 * 3362491 * 2
def baseEnd_3362491 : Nat := 575524693139102990732897

theorem tailTrace_3362491 : CollatzResearch.WordTrace tailWord_3362491 prefixEnd_3362491 575524693139102990732897 := by
  unfold tailWord_3362491
  simp only [CollatzResearch.WordTrace]
  refine ⟨122640122061276849588119327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81760081374184566392079551 122640122061276849588119327)
  ·
    refine ⟨183960183091915274382178991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122640122061276849588119327 183960183091915274382178991)
    ·
      refine ⟨275940274637872911573268487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183960183091915274382178991 275940274637872911573268487)
      ·
        refine ⟨413910411956809367359902731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275940274637872911573268487 413910411956809367359902731)
        ·
          refine ⟨620865617935214051039854097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413910411956809367359902731 620865617935214051039854097)
          ·
            refine ⟨465649213451410538279890573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620865617935214051039854097 465649213451410538279890573)
            ·
              refine ⟨174618455044278951854958965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465649213451410538279890573 174618455044278951854958965)
              ·
                refine ⟨16370480160401151736402403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 174618455044278951854958965 16370480160401151736402403)
                ·
                  refine ⟨24555720240601727604603605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16370480160401151736402403 24555720240601727604603605)
                  ·
                    refine ⟨575524693139102990732897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24555720240601727604603605 575524693139102990732897)
                    ·
                      rfl

theorem cell23_3362491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 7].length) (baseStart_3362491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362491 prefixEnd_3362491 := by exact prefixLift 3362491
  have htrace : WordTrace (prefixWord ++ tailWord_3362491) baseStart_3362491 baseEnd_3362491 := by
    simpa [prefixWord, tailWord_3362491, baseEnd_3362491] using wordTrace_append hprefix tailTrace_3362491
  have hstable : (prefixWord ++ tailWord_3362491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362491).length < 2 ^ (prefixWord ++ tailWord_3362491).sum := by decide
  have hdescent : baseEnd_3362491 < baseStart_3362491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362501 : List Nat := [1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 7]
def baseStart_3362501 : Nat := 118140960795 + 3362501 * 2 ^ 59
def prefixEnd_3362501 : Nat := 4983230072969 + 3 ^ 40 * 3362501 * 2
def baseEnd_3362501 : Nat := 1726579214223853933073645

theorem tailTrace_3362501 : CollatzResearch.WordTrace tailWord_3362501 prefixEnd_3362501 1726579214223853933073645 := by
  unfold tailWord_3362501
  simp only [CollatzResearch.WordTrace]
  refine ⟨122640486791240621295983357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81760324527493747530655571 122640486791240621295983357)
  ·
    refine ⟨45990182546715232985993759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122640486791240621295983357 45990182546715232985993759)
    ·
      refine ⟨68985273820072849478990639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45990182546715232985993759 68985273820072849478990639)
      ·
        refine ⟨103477910730109274218485959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68985273820072849478990639 103477910730109274218485959)
        ·
          refine ⟨155216866095163911327728939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103477910730109274218485959 155216866095163911327728939)
          ·
            refine ⟨232825299142745866991593409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155216866095163911327728939 232825299142745866991593409)
            ·
              refine ⟨174618974357059400243695057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232825299142745866991593409 174618974357059400243695057)
              ·
                refine ⟨130964230767794550182771293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174618974357059400243695057 130964230767794550182771293)
                ·
                  refine ⟨49111586537922956318539235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 130964230767794550182771293 49111586537922956318539235)
                  ·
                    refine ⟨73667379806884434477808853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49111586537922956318539235 73667379806884434477808853)
                    ·
                      refine ⟨1726579214223853933073645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73667379806884434477808853 1726579214223853933073645)
                      ·
                        rfl

theorem cell23_3362501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 2, 3, 1, 7].length) (baseStart_3362501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362501 prefixEnd_3362501 := by exact prefixLift 3362501
  have htrace : WordTrace (prefixWord ++ tailWord_3362501) baseStart_3362501 baseEnd_3362501 := by
    simpa [prefixWord, tailWord_3362501, baseEnd_3362501] using wordTrace_append hprefix tailTrace_3362501
  have hstable : (prefixWord ++ tailWord_3362501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362501).length < 2 ^ (prefixWord ++ tailWord_3362501).sum := by decide
  have hdescent : baseEnd_3362501 < baseStart_3362501 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362528 : List Nat := [2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_3362528 : Nat := 118140960795 + 3362528 * 2 ^ 59
def prefixEnd_3362528 : Nat := 4983230072969 + 3 ^ 40 * 3362528 * 2
def baseEnd_3362528 : Nat := 1726593078201525327436021

theorem tailTrace_3362528 : CollatzResearch.WordTrace tailWord_3362528 prefixEnd_3362528 1726593078201525327436021 := by
  unfold tailWord_3362528
  simp only [CollatzResearch.WordTrace]
  refine ⟨61320735781071402453608119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81760981041428536604810825 61320735781071402453608119)
  ·
    refine ⟨91981103671607103680412179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61320735781071402453608119 91981103671607103680412179)
    ·
      refine ⟨137971655507410655520618269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91981103671607103680412179 137971655507410655520618269)
      ·
        refine ⟨51739370815278995820231851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137971655507410655520618269 51739370815278995820231851)
        ·
          refine ⟨77609056222918493730347777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51739370815278995820231851 77609056222918493730347777)
          ·
            refine ⟨58206792167188870297760833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77609056222918493730347777 58206792167188870297760833)
            ·
              refine ⟨43655094125391652723320625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58206792167188870297760833 43655094125391652723320625)
              ·
                refine ⟨32741320594043739542490469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43655094125391652723320625 32741320594043739542490469)
                ·
                  refine ⟨6138997611383201164216963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32741320594043739542490469 6138997611383201164216963)
                  ·
                    refine ⟨9208496417074801746325445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6138997611383201164216963 9208496417074801746325445)
                    ·
                      refine ⟨1726593078201525327436021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9208496417074801746325445 1726593078201525327436021)
                      ·
                        rfl

theorem cell23_3362528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_3362528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362528 prefixEnd_3362528 := by exact prefixLift 3362528
  have htrace : WordTrace (prefixWord ++ tailWord_3362528) baseStart_3362528 baseEnd_3362528 := by
    simpa [prefixWord, tailWord_3362528, baseEnd_3362528] using wordTrace_append hprefix tailTrace_3362528
  have hstable : (prefixWord ++ tailWord_3362528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362528).length < 2 ^ (prefixWord ++ tailWord_3362528).sum := by decide
  have hdescent : baseEnd_3362528 < baseStart_3362528 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362545 : List Nat := [1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 4]
def baseStart_3362545 : Nat := 118140960795 + 3362545 * 2 ^ 59
def prefixEnd_3362545 : Nat := 4983230072969 + 3 ^ 40 * 3362545 * 2
def baseEnd_3362545 : Nat := 1726601807372651760923443

theorem tailTrace_3362545 : CollatzResearch.WordTrace tailWord_3362545 prefixEnd_3362545 1726601807372651760923443 := by
  unfold tailWord_3362545
  simp only [CollatzResearch.WordTrace]
  refine ⟨122642091603081216810585089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81761394402054144540390059 122642091603081216810585089)
  ·
    refine ⟨91981568702310912607938817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122642091603081216810585089 91981568702310912607938817)
    ·
      refine ⟨68986176526733184455954113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91981568702310912607938817 68986176526733184455954113)
      ·
        refine ⟨51739632395049888341965585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68986176526733184455954113 51739632395049888341965585)
        ·
          refine ⟨38804724296287416256474189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51739632395049888341965585 38804724296287416256474189)
          ·
            refine ⟨14551771611107781096177821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38804724296287416256474189 14551771611107781096177821)
            ·
              refine ⟨5456914354165417911066683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14551771611107781096177821 5456914354165417911066683)
              ·
                refine ⟨8185371531248126866600025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5456914354165417911066683 8185371531248126866600025)
                ·
                  refine ⟨6139028648436095149950019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8185371531248126866600025 6139028648436095149950019)
                  ·
                    refine ⟨9208542972654142724925029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6139028648436095149950019 9208542972654142724925029)
                    ·
                      refine ⟨1726601807372651760923443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9208542972654142724925029 1726601807372651760923443)
                      ·
                        rfl

theorem cell23_3362545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_3362545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362545 prefixEnd_3362545 := by exact prefixLift 3362545
  have htrace : WordTrace (prefixWord ++ tailWord_3362545) baseStart_3362545 baseEnd_3362545 := by
    simpa [prefixWord, tailWord_3362545, baseEnd_3362545] using wordTrace_append hprefix tailTrace_3362545
  have hstable : (prefixWord ++ tailWord_3362545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362545).length < 2 ^ (prefixWord ++ tailWord_3362545).sum := by decide
  have hdescent : baseEnd_3362545 < baseStart_3362545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362562 : List Nat := [3, 4, 1, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_3362562 : Nat := 118140960795 + 3362562 * 2 ^ 59
def prefixEnd_3362562 : Nat := 4983230072969 + 3 ^ 40 * 3362562 * 2
def baseEnd_3362562 : Nat := 1726610536543778194410865

theorem tailTrace_3362562 : CollatzResearch.WordTrace tailWord_3362562 prefixEnd_3362562 1726610536543778194410865 := by
  unfold tailWord_3362562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30660677911004907178488485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81761807762679752475969293 30660677911004907178488485)
  ·
    refine ⟨5748877108313420095966591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30660677911004907178488485 5748877108313420095966591)
    ·
      refine ⟨8623315662470130143949887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5748877108313420095966591 8623315662470130143949887)
      ·
        refine ⟨12934973493705195215924831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8623315662470130143949887 12934973493705195215924831)
        ·
          refine ⟨19402460240557792823887247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12934973493705195215924831 19402460240557792823887247)
          ·
            refine ⟨29103690360836689235830871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19402460240557792823887247 29103690360836689235830871)
            ·
              refine ⟨43655535541255033853746307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29103690360836689235830871 43655535541255033853746307)
              ·
                refine ⟨65483303311882550780619461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43655535541255033853746307 65483303311882550780619461)
                ·
                  refine ⟨12278119370977978271366149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65483303311882550780619461 12278119370977978271366149)
                  ·
                    refine ⟨2302147382058370925881153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12278119370977978271366149 2302147382058370925881153)
                    ·
                      refine ⟨1726610536543778194410865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2302147382058370925881153 1726610536543778194410865)
                      ·
                        rfl

theorem cell23_3362562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_3362562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362562 prefixEnd_3362562 := by exact prefixLift 3362562
  have htrace : WordTrace (prefixWord ++ tailWord_3362562) baseStart_3362562 baseEnd_3362562 := by
    simpa [prefixWord, tailWord_3362562, baseEnd_3362562] using wordTrace_append hprefix tailTrace_3362562
  have hstable : (prefixWord ++ tailWord_3362562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362562).length < 2 ^ (prefixWord ++ tailWord_3362562).sum := by decide
  have hdescent : baseEnd_3362562 < baseStart_3362562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362568 : List Nat := [2, 1, 3, 2, 2, 1, 3, 1, 8]
def baseStart_3362568 : Nat := 118140960795 + 3362568 * 2 ^ 59
def prefixEnd_3362568 : Nat := 4983230072969 + 3 ^ 40 * 3362568 * 2
def baseEnd_3362568 : Nat := 191845957491967241215093

theorem tailTrace_3362568 : CollatzResearch.WordTrace tailWord_3362568 prefixEnd_3362568 191845957491967241215093 := by
  unfold tailWord_3362568
  simp only [CollatzResearch.WordTrace]
  refine ⟨61321465240998945869336179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81761953654665261159114905 61321465240998945869336179)
  ·
    refine ⟨91982197861498418804004269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61321465240998945869336179 91982197861498418804004269)
    ·
      refine ⟨34493324198061907051501601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91982197861498418804004269 34493324198061907051501601)
      ·
        refine ⟨25869993148546430288626201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34493324198061907051501601 25869993148546430288626201)
        ·
          refine ⟨19402494861409822716469651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25869993148546430288626201 19402494861409822716469651)
          ·
            refine ⟨29103742292114734074704477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19402494861409822716469651 29103742292114734074704477)
            ·
              refine ⟨10913903359543025278014179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29103742292114734074704477 10913903359543025278014179)
              ·
                refine ⟨16370855039314537917021269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10913903359543025278014179 16370855039314537917021269)
                ·
                  refine ⟨191845957491967241215093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16370855039314537917021269 191845957491967241215093)
                  ·
                    rfl

theorem cell23_3362568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 3, 1, 8].length) (baseStart_3362568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362568 prefixEnd_3362568 := by exact prefixLift 3362568
  have htrace : WordTrace (prefixWord ++ tailWord_3362568) baseStart_3362568 baseEnd_3362568 := by
    simpa [prefixWord, tailWord_3362568, baseEnd_3362568] using wordTrace_append hprefix tailTrace_3362568
  have hstable : (prefixWord ++ tailWord_3362568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362568).length < 2 ^ (prefixWord ++ tailWord_3362568).sum := by decide
  have hdescent : baseEnd_3362568 < baseStart_3362568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362572 : List Nat := [2, 2, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_3362572 : Nat := 118140960795 + 3362572 * 2 ^ 59
def prefixEnd_3362572 : Nat := 4983230072969 + 3 ^ 40 * 3362572 * 2
def baseEnd_3362572 : Nat := 575538557116774385095273

theorem tailTrace_3362572 : CollatzResearch.WordTrace tailWord_3362572 prefixEnd_3362572 575538557116774385095273 := by
  unfold tailWord_3362572
  simp only [CollatzResearch.WordTrace]
  refine ⟨61321538186991700210908985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81762050915988933614545313 61321538186991700210908985)
  ·
    refine ⟨45991153640243775158181739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61321538186991700210908985 45991153640243775158181739)
    ·
      refine ⟨68986730460365662737272609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45991153640243775158181739 68986730460365662737272609)
      ·
        refine ⟨51740047845274247052954457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68986730460365662737272609 51740047845274247052954457)
        ·
          refine ⟨38805035883955685289715843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51740047845274247052954457 38805035883955685289715843)
          ·
            refine ⟨58207553825933527934573765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38805035883955685289715843 58207553825933527934573765)
            ·
              refine ⟨10913916342362536487732581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58207553825933527934573765 10913916342362536487732581)
              ·
                refine ⟨2046359314192975591449859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10913916342362536487732581 2046359314192975591449859)
                ·
                  refine ⟨3069538971289463387174789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046359314192975591449859 3069538971289463387174789)
                  ·
                    refine ⟨575538557116774385095273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069538971289463387174789 575538557116774385095273)
                    ·
                      rfl

theorem cell23_3362572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_3362572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362572 prefixEnd_3362572 := by exact prefixLift 3362572
  have htrace : WordTrace (prefixWord ++ tailWord_3362572) baseStart_3362572 baseEnd_3362572 := by
    simpa [prefixWord, tailWord_3362572, baseEnd_3362572] using wordTrace_append hprefix tailTrace_3362572
  have hstable : (prefixWord ++ tailWord_3362572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362572).length < 2 ^ (prefixWord ++ tailWord_3362572).sum := by decide
  have hdescent : baseEnd_3362572 < baseStart_3362572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362588 : List Nat := [2, 2, 3, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_3362588 : Nat := 118140960795 + 3362588 * 2 ^ 59
def prefixEnd_3362588 : Nat := 4983230072969 + 3 ^ 40 * 3362588 * 2
def baseEnd_3362588 : Nat := 1726623887040795092685745

theorem tailTrace_3362588 : CollatzResearch.WordTrace tailWord_3362588 prefixEnd_3362588 1726623887040795092685745 := by
  unfold tailWord_3362588
  simp only [CollatzResearch.WordTrace]
  refine ⟨61321829970962717577200209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81762439961283623436266945 61321829970962717577200209)
  ·
    refine ⟨45991372478222038182900157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61321829970962717577200209 45991372478222038182900157)
    ·
      refine ⟨17246764679333264318587559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45991372478222038182900157 17246764679333264318587559)
      ·
        refine ⟨25870147018999896477881339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17246764679333264318587559 25870147018999896477881339)
        ·
          refine ⟨38805220528499844716822009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25870147018999896477881339 38805220528499844716822009)
          ·
            refine ⟨29103915396374883537616507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38805220528499844716822009 29103915396374883537616507)
            ·
              refine ⟨43655873094562325306424761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29103915396374883537616507 43655873094562325306424761)
              ·
                refine ⟨32741904820921743979818571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43655873094562325306424761 32741904820921743979818571)
                ·
                  refine ⟨49112857231382615969727857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32741904820921743979818571 49112857231382615969727857)
                  ·
                    refine ⟨36834642923536961977295893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49112857231382615969727857 36834642923536961977295893)
                    ·
                      refine ⟨1726623887040795092685745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36834642923536961977295893 1726623887040795092685745)
                      ·
                        rfl

theorem cell23_3362588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_3362588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362588 prefixEnd_3362588 := by exact prefixLift 3362588
  have htrace : WordTrace (prefixWord ++ tailWord_3362588) baseStart_3362588 baseEnd_3362588 := by
    simpa [prefixWord, tailWord_3362588, baseEnd_3362588] using wordTrace_append hprefix tailTrace_3362588
  have hstable : (prefixWord ++ tailWord_3362588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362588).length < 2 ^ (prefixWord ++ tailWord_3362588).sum := by decide
  have hdescent : baseEnd_3362588 < baseStart_3362588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362666 : List Nat := [3, 1, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_3362666 : Nat := 118140960795 + 3362666 * 2 ^ 59
def prefixEnd_3362666 : Nat := 4983230072969 + 3 ^ 40 * 3362666 * 2
def baseEnd_3362666 : Nat := 575554646177281929170129

theorem tailTrace_3362666 : CollatzResearch.WordTrace tailWord_3362666 prefixEnd_3362666 575554646177281929170129 := by
  unfold tailWord_3362666
  simp only [CollatzResearch.WordTrace]
  refine ⟨30661626208910713618934963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81764336557095236317159901 30661626208910713618934963)
  ·
    refine ⟨45992439313366070428402445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30661626208910713618934963 45992439313366070428402445)
    ·
      refine ⟨17247164742512276410650917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45992439313366070428402445 17247164742512276410650917)
      ·
        refine ⟨3233843389221051826997047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17247164742512276410650917 3233843389221051826997047)
        ·
          refine ⟨4850765083831577740495571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233843389221051826997047 4850765083831577740495571)
          ·
            refine ⟨7276147625747366610743357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850765083831577740495571 7276147625747366610743357)
            ·
              refine ⟨2728555359655262479028759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7276147625747366610743357 2728555359655262479028759)
              ·
                refine ⟨4092833039482893718543139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728555359655262479028759 4092833039482893718543139)
                ·
                  refine ⟨6139249559224340577814709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4092833039482893718543139 6139249559224340577814709)
                  ·
                    refine ⟨575554646177281929170129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6139249559224340577814709 575554646177281929170129)
                    ·
                      rfl

theorem cell23_3362666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_3362666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362666 prefixEnd_3362666 := by exact prefixLift 3362666
  have htrace : WordTrace (prefixWord ++ tailWord_3362666) baseStart_3362666 baseEnd_3362666 := by
    simpa [prefixWord, tailWord_3362666, baseEnd_3362666] using wordTrace_append hprefix tailTrace_3362666
  have hstable : (prefixWord ++ tailWord_3362666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362666).length < 2 ^ (prefixWord ++ tailWord_3362666).sum := by decide
  have hdescent : baseEnd_3362666 < baseStart_3362666 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362685 : List Nat := [1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_3362685 : Nat := 118140960795 + 3362685 * 2 ^ 59
def prefixEnd_3362685 : Nat := 4983230072969 + 3 ^ 40 * 3362685 * 2
def baseEnd_3362685 : Nat := 1726673694664281213172799

theorem tailTrace_3362685 : CollatzResearch.WordTrace tailWord_3362685 prefixEnd_3362685 1726673694664281213172799 := by
  unfold tailWord_3362685
  simp only [CollatzResearch.WordTrace]
  refine ⟨122647197822574020720681509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81764798548382680480454339 122647197822574020720681509)
  ·
    refine ⟨22996349591732628885127783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122647197822574020720681509 22996349591732628885127783)
    ·
      refine ⟨34494524387598943327691675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22996349591732628885127783 34494524387598943327691675)
      ·
        refine ⟨51741786581398414991537513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34494524387598943327691675 51741786581398414991537513)
        ·
          refine ⟨38806339936048811243653135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51741786581398414991537513 38806339936048811243653135)
          ·
            refine ⟨58209509904073216865479703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38806339936048811243653135 58209509904073216865479703)
            ·
              refine ⟨87314264856109825298219555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58209509904073216865479703 87314264856109825298219555)
              ·
                refine ⟨130971397284164737947329333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87314264856109825298219555 130971397284164737947329333)
                ·
                  refine ⟨12278568495390444182562125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130971397284164737947329333 12278568495390444182562125)
                  ·
                    refine ⟨4604463185771416568460797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12278568495390444182562125 4604463185771416568460797)
                    ·
                      refine ⟨1726673694664281213172799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4604463185771416568460797 1726673694664281213172799)
                      ·
                        rfl

theorem cell23_3362685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_3362685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362685 prefixEnd_3362685 := by exact prefixLift 3362685
  have htrace : WordTrace (prefixWord ++ tailWord_3362685) baseStart_3362685 baseEnd_3362685 := by
    simpa [prefixWord, tailWord_3362685, baseEnd_3362685] using wordTrace_append hprefix tailTrace_3362685
  have hstable : (prefixWord ++ tailWord_3362685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362685).length < 2 ^ (prefixWord ++ tailWord_3362685).sum := by decide
  have hdescent : baseEnd_3362685 < baseStart_3362685 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362688 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 1, 9]
def baseStart_3362688 : Nat := 118140960795 + 3362688 * 2 ^ 59
def prefixEnd_3362688 : Nat := 4983230072969 + 3 ^ 40 * 3362688 * 2
def baseEnd_3362688 : Nat := 575558411702081567145095

theorem tailTrace_3362688 : CollatzResearch.WordTrace tailWord_3362688 prefixEnd_3362688 575558411702081567145095 := by
  unfold tailWord_3362688
  simp only [CollatzResearch.WordTrace]
  refine ⟨61323653620781576116520359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81764871494375434822027145 61323653620781576116520359)
  ·
    refine ⟨91985480431172364174780539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61323653620781576116520359 91985480431172364174780539)
    ·
      refine ⟨137978220646758546262170809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91985480431172364174780539 137978220646758546262170809)
      ·
        refine ⟨103483665485068909696628107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137978220646758546262170809 103483665485068909696628107)
        ·
          refine ⟨155225498227603364544942161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103483665485068909696628107 155225498227603364544942161)
          ·
            refine ⟨116419123670702523408706621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155225498227603364544942161 116419123670702523408706621)
            ·
              refine ⟨43657171376513446278264983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116419123670702523408706621 43657171376513446278264983)
              ·
                refine ⟨65485757064770169417397475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43657171376513446278264983 65485757064770169417397475)
                ·
                  refine ⟨98228635597155254126096213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65485757064770169417397475 98228635597155254126096213)
                  ·
                    refine ⟨575558411702081567145095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 98228635597155254126096213 575558411702081567145095)
                    ·
                      rfl

theorem cell23_3362688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_3362688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362688 prefixEnd_3362688 := by exact prefixLift 3362688
  have htrace : WordTrace (prefixWord ++ tailWord_3362688) baseStart_3362688 baseEnd_3362688 := by
    simpa [prefixWord, tailWord_3362688, baseEnd_3362688] using wordTrace_append hprefix tailTrace_3362688
  have hstable : (prefixWord ++ tailWord_3362688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362688).length < 2 ^ (prefixWord ++ tailWord_3362688).sum := by decide
  have hdescent : baseEnd_3362688 < baseStart_3362688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362799 : List Nat := [1, 1, 2, 1, 4, 2, 5, 2, 5]
def baseStart_3362799 : Nat := 118140960795 + 3362799 * 2 ^ 59
def prefixEnd_3362799 : Nat := 4983230072969 + 3 ^ 40 * 3362799 * 2
def baseEnd_3362799 : Nat := 191859136828765974127475

theorem tailTrace_3362799 : CollatzResearch.WordTrace tailWord_3362799 prefixEnd_3362799 191859136828765974127475 := by
  unfold tailWord_3362799
  simp only [CollatzResearch.WordTrace]
  refine ⟨122651355744161018190331451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81767570496107345460220967 122651355744161018190331451)
  ·
    refine ⟨183977033616241527285497177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122651355744161018190331451 183977033616241527285497177)
    ·
      refine ⟨137982775212181145464122883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183977033616241527285497177 137982775212181145464122883)
      ·
        refine ⟨206974162818271718196184325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137982775212181145464122883 206974162818271718196184325)
        ·
          refine ⟨38807655528425947161784561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206974162818271718196184325 38807655528425947161784561)
          ·
            refine ⟨29105741646319460371338421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38807655528425947161784561 29105741646319460371338421)
            ·
              refine ⟨2728663279342449409812977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29105741646319460371338421 2728663279342449409812977)
              ·
                refine ⟨2046497459506837057359733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728663279342449409812977 2046497459506837057359733)
                ·
                  refine ⟨191859136828765974127475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2046497459506837057359733 191859136828765974127475)
                  ·
                    rfl

theorem cell23_3362799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 5, 2, 5].length) (baseStart_3362799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362799 prefixEnd_3362799 := by exact prefixLift 3362799
  have htrace : WordTrace (prefixWord ++ tailWord_3362799) baseStart_3362799 baseEnd_3362799 := by
    simpa [prefixWord, tailWord_3362799, baseEnd_3362799] using wordTrace_append hprefix tailTrace_3362799
  have hstable : (prefixWord ++ tailWord_3362799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362799).length < 2 ^ (prefixWord ++ tailWord_3362799).sum := by decide
  have hdescent : baseEnd_3362799 < baseStart_3362799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362815 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_3362815 : Nat := 118140960795 + 3362815 * 2 ^ 59
def prefixEnd_3362815 : Nat := 4983230072969 + 3 ^ 40 * 3362815 * 2
def baseEnd_3362815 : Nat := 1726740447149365704547201

theorem tailTrace_3362815 : CollatzResearch.WordTrace tailWord_3362815 prefixEnd_3362815 1726740447149365704547201 := by
  unfold tailWord_3362815
  simp only [CollatzResearch.WordTrace]
  refine ⟨122651939312103052922913899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81767959541402035281942599 122651939312103052922913899)
  ·
    refine ⟨183977908968154579384370849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122651939312103052922913899 183977908968154579384370849)
    ·
      refine ⟨137983431726115934538278137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183977908968154579384370849 137983431726115934538278137)
      ·
        refine ⟨103487573794586950903708603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137983431726115934538278137 103487573794586950903708603)
        ·
          refine ⟨155231360691880426355562905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103487573794586950903708603 155231360691880426355562905)
          ·
            refine ⟨116423520518910319766672179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155231360691880426355562905 116423520518910319766672179)
            ·
              refine ⟨174635280778365479650008269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116423520518910319766672179 174635280778365479650008269)
              ·
                refine ⟨65488230291887054868753101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174635280778365479650008269 65488230291887054868753101)
                ·
                  refine ⟨24558086359457645575782413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65488230291887054868753101 24558086359457645575782413)
                  ·
                    refine ⟨9209282384796617090918405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24558086359457645575782413 9209282384796617090918405)
                    ·
                      refine ⟨1726740447149365704547201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9209282384796617090918405 1726740447149365704547201)
                      ·
                        rfl

theorem cell23_3362815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_3362815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362815 prefixEnd_3362815 := by exact prefixLift 3362815
  have htrace : WordTrace (prefixWord ++ tailWord_3362815) baseStart_3362815 baseEnd_3362815 := by
    simpa [prefixWord, tailWord_3362815, baseEnd_3362815] using wordTrace_append hprefix tailTrace_3362815
  have hstable : (prefixWord ++ tailWord_3362815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362815).length < 2 ^ (prefixWord ++ tailWord_3362815).sum := by decide
  have hdescent : baseEnd_3362815 < baseStart_3362815 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362832 : List Nat := [2, 1, 1, 1, 1, 1, 1, 6, 1, 6, 2]
def baseStart_3362832 : Nat := 118140960795 + 3362832 * 2 ^ 59
def prefixEnd_3362832 : Nat := 4983230072969 + 3 ^ 40 * 3362832 * 2
def baseEnd_3362832 : Nat := 1726749176320492138034623

theorem tailTrace_3362832 : CollatzResearch.WordTrace tailWord_3362832 prefixEnd_3362832 1726749176320492138034623 := by
  unfold tailWord_3362832
  simp only [CollatzResearch.WordTrace]
  refine ⟨61326279676520732413141375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81768372902027643217521833 61326279676520732413141375)
  ·
    refine ⟨91989419514781098619712063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61326279676520732413141375 91989419514781098619712063)
    ·
      refine ⟨137984129272171647929568095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91989419514781098619712063 137984129272171647929568095)
      ·
        refine ⟨206976193908257471894352143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137984129272171647929568095 206976193908257471894352143)
        ·
          refine ⟨310464290862386207841528215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206976193908257471894352143 310464290862386207841528215)
          ·
            refine ⟨465696436293579311762292323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310464290862386207841528215 465696436293579311762292323)
            ·
              refine ⟨698544654440368967643438485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465696436293579311762292323 698544654440368967643438485)
              ·
                refine ⟨32744280676892295358286179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 698544654440368967643438485 32744280676892295358286179)
                ·
                  refine ⟨49116421015338443037429269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32744280676892295358286179 49116421015338443037429269)
                  ·
                    refine ⟨2302332235093989517379497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49116421015338443037429269 2302332235093989517379497)
                    ·
                      refine ⟨1726749176320492138034623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2302332235093989517379497 1726749176320492138034623)
                      ·
                        rfl

theorem cell23_3362832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 6, 1, 6, 2].length) (baseStart_3362832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362832 prefixEnd_3362832 := by exact prefixLift 3362832
  have htrace : WordTrace (prefixWord ++ tailWord_3362832) baseStart_3362832 baseEnd_3362832 := by
    simpa [prefixWord, tailWord_3362832, baseEnd_3362832] using wordTrace_append hprefix tailTrace_3362832
  have hstable : (prefixWord ++ tailWord_3362832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362832).length < 2 ^ (prefixWord ++ tailWord_3362832).sum := by decide
  have hdescent : baseEnd_3362832 < baseStart_3362832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362875 : List Nat := [1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 6]
def baseStart_3362875 : Nat := 118140960795 + 3362875 * 2 ^ 59
def prefixEnd_3362875 : Nat := 4983230072969 + 3 ^ 40 * 3362875 * 2
def baseEnd_3362875 : Nat := 1726771255988635469796925

theorem tailTrace_3362875 : CollatzResearch.WordTrace tailWord_3362875 prefixEnd_3362875 1726771255988635469796925 := by
  unfold tailWord_3362875
  simp only [CollatzResearch.WordTrace]
  refine ⟨122654127691885683170098079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81769418461257122113398719 122654127691885683170098079)
  ·
    refine ⟨183981191537828524755147119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122654127691885683170098079 183981191537828524755147119)
    ·
      refine ⟨275971787306742787132720679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183981191537828524755147119 275971787306742787132720679)
      ·
        refine ⟨413957680960114180699081019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275971787306742787132720679 413957680960114180699081019)
        ·
          refine ⟨620936521440171271048621529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413957680960114180699081019 620936521440171271048621529)
          ·
            refine ⟨465702391080128453286466147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 620936521440171271048621529 465702391080128453286466147)
            ·
              refine ⟨698553586620192679929699221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 465702391080128453286466147 698553586620192679929699221)
              ·
                refine ⟨32744699372821531871704651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 698553586620192679929699221 32744699372821531871704651)
                ·
                  refine ⟨49117049059232297807556977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32744699372821531871704651 49117049059232297807556977)
                  ·
                    refine ⟨36837786794424223355667733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49117049059232297807556977 36837786794424223355667733)
                    ·
                      refine ⟨1726771255988635469796925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36837786794424223355667733 1726771255988635469796925)
                      ·
                        rfl

theorem cell23_3362875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_3362875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362875 prefixEnd_3362875 := by exact prefixLift 3362875
  have htrace : WordTrace (prefixWord ++ tailWord_3362875) baseStart_3362875 baseEnd_3362875 := by
    simpa [prefixWord, tailWord_3362875, baseEnd_3362875] using wordTrace_append hprefix tailTrace_3362875
  have hstable : (prefixWord ++ tailWord_3362875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362875).length < 2 ^ (prefixWord ++ tailWord_3362875).sum := by decide
  have hdescent : baseEnd_3362875 < baseStart_3362875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362886 : List Nat := [6, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_3362886 : Nat := 118140960795 + 3362886 * 2 ^ 59
def prefixEnd_3362886 : Nat := 4983230072969 + 3 ^ 40 * 3362886 * 2
def baseEnd_3362886 : Nat := 1726776904275834926759375

theorem tailTrace_3362886 : CollatzResearch.WordTrace tailWord_3362886 prefixEnd_3362886 1726776904275834926759375 := by
  unfold tailWord_3362886
  simp only [CollatzResearch.WordTrace]
  refine ⟨3832954027963932251523391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81769685929897221365832341 3832954027963932251523391)
  ·
    refine ⟨5749431041945898377285087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3832954027963932251523391 5749431041945898377285087)
    ·
      refine ⟨8624146562918847565927631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749431041945898377285087 8624146562918847565927631)
      ·
        refine ⟨12936219844378271348891447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8624146562918847565927631 12936219844378271348891447)
        ·
          refine ⟨19404329766567407023337171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12936219844378271348891447 19404329766567407023337171)
          ·
            refine ⟨29106494649851110535005757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19404329766567407023337171 29106494649851110535005757)
            ·
              refine ⟨10914935493694166450627159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29106494649851110535005757 10914935493694166450627159)
              ·
                refine ⟨16372403240541249675940739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10914935493694166450627159 16372403240541249675940739)
                ·
                  refine ⟨24558604860811874513911109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16372403240541249675940739 24558604860811874513911109)
                  ·
                    refine ⟨4604738411402226471358333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24558604860811874513911109 4604738411402226471358333)
                    ·
                      refine ⟨1726776904275834926759375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4604738411402226471358333 1726776904275834926759375)
                      ·
                        rfl

theorem cell23_3362886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_3362886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362886 prefixEnd_3362886 := by exact prefixLift 3362886
  have htrace : WordTrace (prefixWord ++ tailWord_3362886) baseStart_3362886 baseEnd_3362886 := by
    simpa [prefixWord, tailWord_3362886, baseEnd_3362886] using wordTrace_append hprefix tailTrace_3362886
  have hstable : (prefixWord ++ tailWord_3362886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362886).length < 2 ^ (prefixWord ++ tailWord_3362886).sum := by decide
  have hdescent : baseEnd_3362886 < baseStart_3362886 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362893 : List Nat := [1, 6, 1, 1, 1, 1, 4, 3, 1, 4]
def baseStart_3362893 : Nat := 118140960795 + 3362893 * 2 ^ 59
def prefixEnd_3362893 : Nat := 4983230072969 + 3 ^ 40 * 3362893 * 2
def baseEnd_3362893 : Nat := 575593499546805466457281

theorem tailTrace_3362893 : CollatzResearch.WordTrace tailWord_3362893 prefixEnd_3362893 575593499546805466457281 := by
  unfold tailWord_3362893
  simp only [CollatzResearch.WordTrace]
  refine ⟨122654784205820472244253333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81769856137213648162835555 122654784205820472244253333)
  ·
    refine ⟨5749443009647834636449375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122654784205820472244253333 5749443009647834636449375)
    ·
      refine ⟨8624164514471751954674063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5749443009647834636449375 8624164514471751954674063)
      ·
        refine ⟨12936246771707627932011095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8624164514471751954674063 12936246771707627932011095)
        ·
          refine ⟨19404370157561441898016643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12936246771707627932011095 19404370157561441898016643)
          ·
            refine ⟨29106555236342162847024965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19404370157561441898016643 29106555236342162847024965)
            ·
              refine ⟨5457479106814155533817181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29106555236342162847024965 5457479106814155533817181)
              ·
                refine ⟨2046554665055308325181443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5457479106814155533817181 2046554665055308325181443)
                ·
                  refine ⟨3069831997582962487772165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046554665055308325181443 3069831997582962487772165)
                  ·
                    refine ⟨575593499546805466457281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069831997582962487772165 575593499546805466457281)
                    ·
                      rfl

theorem cell23_3362893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_3362893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362893 prefixEnd_3362893 := by exact prefixLift 3362893
  have htrace : WordTrace (prefixWord ++ tailWord_3362893) baseStart_3362893 baseEnd_3362893 := by
    simpa [prefixWord, tailWord_3362893, baseEnd_3362893] using wordTrace_append hprefix tailTrace_3362893
  have hstable : (prefixWord ++ tailWord_3362893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362893).length < 2 ^ (prefixWord ++ tailWord_3362893).sum := by decide
  have hdescent : baseEnd_3362893 < baseStart_3362893 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362895 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_3362895 : Nat := 118140960795 + 3362895 * 2 ^ 59
def prefixEnd_3362895 : Nat := 4983230072969 + 3 ^ 40 * 3362895 * 2
def baseEnd_3362895 : Nat := 1726781525601725391546833

theorem tailTrace_3362895 : CollatzResearch.WordTrace tailWord_3362895 prefixEnd_3362895 1726781525601725391546833 := by
  unfold tailWord_3362895
  simp only [CollatzResearch.WordTrace]
  refine ⟨122654857151813226585826139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81769904767875484390550759 122654857151813226585826139)
  ·
    refine ⟨183982285727719839878739209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122654857151813226585826139 183982285727719839878739209)
    ·
      refine ⟨137986714295789879909054407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183982285727719839878739209 137986714295789879909054407)
      ·
        refine ⟨206980071443684819863581611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137986714295789879909054407 206980071443684819863581611)
        ·
          refine ⟨310470107165527229795372417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206980071443684819863581611 310470107165527229795372417)
          ·
            refine ⟨232852580374145422346529313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310470107165527229795372417 232852580374145422346529313)
            ·
              refine ⟨174639435280609066759896985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232852580374145422346529313 174639435280609066759896985)
              ·
                refine ⟨130979576460456800069922739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174639435280609066759896985 130979576460456800069922739)
                ·
                  refine ⟨196469364690685200104884109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130979576460456800069922739 196469364690685200104884109)
                  ·
                    refine ⟨73676011759006950039331541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 196469364690685200104884109 73676011759006950039331541)
                    ·
                      refine ⟨1726781525601725391546833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73676011759006950039331541 1726781525601725391546833)
                      ·
                        rfl

theorem cell23_3362895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_3362895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362895 prefixEnd_3362895 := by exact prefixLift 3362895
  have htrace : WordTrace (prefixWord ++ tailWord_3362895) baseStart_3362895 baseEnd_3362895 := by
    simpa [prefixWord, tailWord_3362895, baseEnd_3362895] using wordTrace_append hprefix tailTrace_3362895
  have hstable : (prefixWord ++ tailWord_3362895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362895).length < 2 ^ (prefixWord ++ tailWord_3362895).sum := by decide
  have hdescent : baseEnd_3362895 < baseStart_3362895 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362909 : List Nat := [1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3362909 : Nat := 118140960795 + 3362909 * 2 ^ 59
def prefixEnd_3362909 : Nat := 4983230072969 + 3 ^ 40 * 3362909 * 2
def baseEnd_3362909 : Nat := 1726788714330888336771769

theorem tailTrace_3362909 : CollatzResearch.WordTrace tailWord_3362909 prefixEnd_3362909 1726788714330888336771769 := by
  unfold tailWord_3362909
  simp only [CollatzResearch.WordTrace]
  refine ⟨122655367773762506976835781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81770245182508337984557187 122655367773762506976835781)
  ·
    refine ⟨22997881457580470058156709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122655367773762506976835781 22997881457580470058156709)
    ·
      refine ⟨4312102773296338135904383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22997881457580470058156709 4312102773296338135904383)
      ·
        refine ⟨6468154159944507203856575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312102773296338135904383 6468154159944507203856575)
        ·
          refine ⟨9702231239916760805784863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6468154159944507203856575 9702231239916760805784863)
          ·
            refine ⟨14553346859875141208677295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702231239916760805784863 14553346859875141208677295)
            ·
              refine ⟨21830020289812711813015943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14553346859875141208677295 21830020289812711813015943)
              ·
                refine ⟨32745030434719067719523915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21830020289812711813015943 32745030434719067719523915)
                ·
                  refine ⟨49117545652078601579285873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32745030434719067719523915 49117545652078601579285873)
                  ·
                    refine ⟨36838159239058951184464405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49117545652078601579285873 36838159239058951184464405)
                    ·
                      refine ⟨1726788714330888336771769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36838159239058951184464405 1726788714330888336771769)
                      ·
                        rfl

theorem cell23_3362909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3362909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362909 prefixEnd_3362909 := by exact prefixLift 3362909
  have htrace : WordTrace (prefixWord ++ tailWord_3362909) baseStart_3362909 baseEnd_3362909 := by
    simpa [prefixWord, tailWord_3362909, baseEnd_3362909] using wordTrace_append hprefix tailTrace_3362909
  have hstable : (prefixWord ++ tailWord_3362909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362909).length < 2 ^ (prefixWord ++ tailWord_3362909).sum := by decide
  have hdescent : baseEnd_3362909 < baseStart_3362909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362910 : List Nat := [4, 4, 1, 1, 2, 1, 2, 1, 3, 4]
def baseStart_3362910 : Nat := 118140960795 + 3362910 * 2 ^ 59
def prefixEnd_3362910 : Nat := 4983230072969 + 3 ^ 40 * 3362910 * 2
def baseEnd_3362910 : Nat := 575596409270514277619755

theorem tailTrace_3362910 : CollatzResearch.WordTrace tailWord_3362910 prefixEnd_3362910 575596409270514277619755 := by
  unfold tailWord_3362910
  simp only [CollatzResearch.WordTrace]
  refine ⟨15331925530844860518452773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81770269497839256098414789 15331925530844860518452773)
  ·
    refine ⟨2874736037033411347209895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15331925530844860518452773 2874736037033411347209895)
    ·
      refine ⟨4312104055550117020814843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874736037033411347209895 4312104055550117020814843)
      ·
        refine ⟨6468156083325175531222265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312104055550117020814843 6468156083325175531222265)
        ·
          refine ⟨4851117062493881648416699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6468156083325175531222265 4851117062493881648416699)
          ·
            refine ⟨7276675593740822472625049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851117062493881648416699 7276675593740822472625049)
            ·
              refine ⟨5457506695305616854468787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7276675593740822472625049 5457506695305616854468787)
              ·
                refine ⟨8186260042958425281703181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457506695305616854468787 8186260042958425281703181)
                ·
                  refine ⟨3069847516109409480638693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8186260042958425281703181 3069847516109409480638693)
                  ·
                    refine ⟨575596409270514277619755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069847516109409480638693 575596409270514277619755)
                    ·
                      rfl

theorem cell23_3362910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_3362910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362910 prefixEnd_3362910 := by exact prefixLift 3362910
  have htrace : WordTrace (prefixWord ++ tailWord_3362910) baseStart_3362910 baseEnd_3362910 := by
    simpa [prefixWord, tailWord_3362910, baseEnd_3362910] using wordTrace_append hprefix tailTrace_3362910
  have hstable : (prefixWord ++ tailWord_3362910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362910).length < 2 ^ (prefixWord ++ tailWord_3362910).sum := by decide
  have hdescent : baseEnd_3362910 < baseStart_3362910 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362949 : List Nat := [1, 3, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_3362949 : Nat := 118140960795 + 3362949 * 2 ^ 59
def prefixEnd_3362949 : Nat := 4983230072969 + 3 ^ 40 * 3362949 * 2
def baseEnd_3362949 : Nat := 575603084519022726757195

theorem tailTrace_3362949 : CollatzResearch.WordTrace tailWord_3362949 prefixEnd_3362949 575603084519022726757195 := by
  unfold tailWord_3362949
  simp only [CollatzResearch.WordTrace]
  refine ⟨122656826693617593808291901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81771217795745062538861267 122656826693617593808291901)
  ·
    refine ⟨45996310010106597678109463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122656826693617593808291901 45996310010106597678109463)
    ·
      refine ⟨68994465015159896517164195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45996310010106597678109463 68994465015159896517164195)
      ·
        refine ⟨103491697522739844775746293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68994465015159896517164195 103491697522739844775746293)
        ·
          refine ⟨9702346642756860447726215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103491697522739844775746293 9702346642756860447726215)
          ·
            refine ⟨14553519964135290671589323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702346642756860447726215 14553519964135290671589323)
            ·
              refine ⟨21830279946202936007383985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14553519964135290671589323 21830279946202936007383985)
              ·
                refine ⟨16372709959652202005537989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21830279946202936007383985 16372709959652202005537989)
                ·
                  refine ⟨3069883117434787876038373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16372709959652202005537989 3069883117434787876038373)
                  ·
                    refine ⟨575603084519022726757195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069883117434787876038373 575603084519022726757195)
                    ·
                      rfl

theorem cell23_3362949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_3362949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362949 prefixEnd_3362949 := by exact prefixLift 3362949
  have htrace : WordTrace (prefixWord ++ tailWord_3362949) baseStart_3362949 baseEnd_3362949 := by
    simpa [prefixWord, tailWord_3362949, baseEnd_3362949] using wordTrace_append hprefix tailTrace_3362949
  have hstable : (prefixWord ++ tailWord_3362949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362949).length < 2 ^ (prefixWord ++ tailWord_3362949).sum := by decide
  have hdescent : baseEnd_3362949 < baseStart_3362949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362973 : List Nat := [1, 4, 2, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_3362973 : Nat := 118140960795 + 3362973 * 2 ^ 59
def prefixEnd_3362973 : Nat := 4983230072969 + 3 ^ 40 * 3362973 * 2
def baseEnd_3362973 : Nat := 1726821577092776086371475

theorem tailTrace_3362973 : CollatzResearch.WordTrace tailWord_3362973 prefixEnd_3362973 1726821577092776086371475 := by
  unfold tailWord_3362973
  simp only [CollatzResearch.WordTrace]
  refine ⟨122657702045530645907165573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81771801363687097271443715 122657702045530645907165573)
  ·
    refine ⟨22998319133536996107593545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122657702045530645907165573 22998319133536996107593545)
    ·
      refine ⟨17248739350152747080695159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22998319133536996107593545 17248739350152747080695159)
      ·
        refine ⟨25873109025229120621042739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17248739350152747080695159 25873109025229120621042739)
        ·
          refine ⟨38809663537843680931564109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25873109025229120621042739 38809663537843680931564109)
          ·
            refine ⟨14553623826691380349336541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38809663537843680931564109 14553623826691380349336541)
            ·
              refine ⟨5457608935009267631001203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14553623826691380349336541 5457608935009267631001203)
              ·
                refine ⟨8186413402513901446501805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457608935009267631001203 8186413402513901446501805)
                ·
                  refine ⟨3069905025942713042438177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8186413402513901446501805 3069905025942713042438177)
                  ·
                    refine ⟨2302428769457034781828633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3069905025942713042438177 2302428769457034781828633)
                    ·
                      refine ⟨1726821577092776086371475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2302428769457034781828633 1726821577092776086371475)
                      ·
                        rfl

theorem cell23_3362973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_3362973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362973 prefixEnd_3362973 := by exact prefixLift 3362973
  have htrace : WordTrace (prefixWord ++ tailWord_3362973) baseStart_3362973 baseEnd_3362973 := by
    simpa [prefixWord, tailWord_3362973, baseEnd_3362973] using wordTrace_append hprefix tailTrace_3362973
  have hstable : (prefixWord ++ tailWord_3362973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362973).length < 2 ^ (prefixWord ++ tailWord_3362973).sum := by decide
  have hdescent : baseEnd_3362973 < baseStart_3362973 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3362983 : List Nat := [1, 1, 6, 2, 2, 1, 1, 3, 2, 4]
def baseStart_3362983 : Nat := 118140960795 + 3362983 * 2 ^ 59
def prefixEnd_3362983 : Nat := 4983230072969 + 3 ^ 40 * 3362983 * 2
def baseEnd_3362983 : Nat := 575608903966440349082143

theorem tailTrace_3362983 : CollatzResearch.WordTrace tailWord_3362983 prefixEnd_3362983 575608903966440349082143 := by
  unfold tailWord_3362983
  simp only [CollatzResearch.WordTrace]
  refine ⟨122658066775494417615029603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81772044516996278410019735 122658066775494417615029603)
  ·
    refine ⟨183987100163241626422544405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122658066775494417615029603 183987100163241626422544405)
    ·
      refine ⟨8624395320151951238556769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 183987100163241626422544405 8624395320151951238556769)
      ·
        refine ⟨6468296490113963428917577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8624395320151951238556769 6468296490113963428917577)
        ·
          refine ⟨4851222367585472571688183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6468296490113963428917577 4851222367585472571688183)
          ·
            refine ⟨7276833551378208857532275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851222367585472571688183 7276833551378208857532275)
            ·
              refine ⟨10915250327067313286298413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7276833551378208857532275 10915250327067313286298413)
              ·
                refine ⟨4093218872650242482361905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10915250327067313286298413 4093218872650242482361905)
                ·
                  refine ⟨3069914154487681861771429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4093218872650242482361905 3069914154487681861771429)
                  ·
                    refine ⟨575608903966440349082143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3069914154487681861771429 575608903966440349082143)
                    ·
                      rfl

theorem cell23_3362983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_3362983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3362983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3362983 prefixEnd_3362983 := by exact prefixLift 3362983
  have htrace : WordTrace (prefixWord ++ tailWord_3362983) baseStart_3362983 baseEnd_3362983 := by
    simpa [prefixWord, tailWord_3362983, baseEnd_3362983] using wordTrace_append hprefix tailTrace_3362983
  have hstable : (prefixWord ++ tailWord_3362983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3362983).length < 2 ^ (prefixWord ++ tailWord_3362983).sum := by decide
  have hdescent : baseEnd_3362983 < baseStart_3362983 := by decide
  rcases family_descends (prefixWord ++ tailWord_3362983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363002 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5]
def baseStart_3363002 : Nat := 118140960795 + 3363002 * 2 ^ 59
def prefixEnd_3363002 : Nat := 4983230072969 + 3 ^ 40 * 3363002 * 2
def baseEnd_3363002 : Nat := 1726836468031756472908841

theorem tailTrace_3363002 : CollatzResearch.WordTrace tailWord_3363002 prefixEnd_3363002 1726836468031756472908841 := by
  unfold tailWord_3363002
  simp only [CollatzResearch.WordTrace]
  refine ⟨30664689940606395964992815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81772506508283722573314173 30664689940606395964992815)
  ·
    refine ⟨45997034910909593947489223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30664689940606395964992815 45997034910909593947489223)
    ·
      refine ⟨68995552366364390921233835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45997034910909593947489223 68995552366364390921233835)
      ·
        refine ⟨103493328549546586381850753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68995552366364390921233835 103493328549546586381850753)
        ·
          refine ⟨77619996412159939786388065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103493328549546586381850753 77619996412159939786388065)
          ·
            refine ⟨58214997309119954839791049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77619996412159939786388065 58214997309119954839791049)
            ·
              refine ⟨43661247981839966129843287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58214997309119954839791049 43661247981839966129843287)
              ·
                refine ⟨65491871972759949194764931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43661247981839966129843287 65491871972759949194764931)
                ·
                  refine ⟨98237807959139923792147397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65491871972759949194764931 98237807959139923792147397)
                  ·
                    refine ⟨18419588992338735711027637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 98237807959139923792147397 18419588992338735711027637)
                    ·
                      refine ⟨1726836468031756472908841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18419588992338735711027637 1726836468031756472908841)
                      ·
                        rfl

theorem cell23_3363002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5].length) (baseStart_3363002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363002 prefixEnd_3363002 := by exact prefixLift 3363002
  have htrace : WordTrace (prefixWord ++ tailWord_3363002) baseStart_3363002 baseEnd_3363002 := by
    simpa [prefixWord, tailWord_3363002, baseEnd_3363002] using wordTrace_append hprefix tailTrace_3363002
  have hstable : (prefixWord ++ tailWord_3363002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363002).length < 2 ^ (prefixWord ++ tailWord_3363002).sum := by decide
  have hdescent : baseEnd_3363002 < baseStart_3363002 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363010 : List Nat := [3, 5, 1, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_3363010 : Nat := 118140960795 + 3363010 * 2 ^ 59
def prefixEnd_3363010 : Nat := 4983230072969 + 3 ^ 40 * 3363010 * 2
def baseEnd_3363010 : Nat := 1726840575876992441608805

theorem tailTrace_3363010 : CollatzResearch.WordTrace tailWord_3363010 prefixEnd_3363010 1726840575876992441608805 := by
  unfold tailWord_3363010
  simp only [CollatzResearch.WordTrace]
  refine ⟨30664762886599150306565621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81772701030931067484174989 30664762886599150306565621)
  ·
    refine ⟨2874821520618670341240527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30664762886599150306565621 2874821520618670341240527)
    ·
      refine ⟨4312232280928005511860791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874821520618670341240527 4312232280928005511860791)
      ·
        refine ⟨6468348421392008267791187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312232280928005511860791 6468348421392008267791187)
        ·
          refine ⟨9702522632088012401686781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6468348421392008267791187 9702522632088012401686781)
          ·
            refine ⟨3638445987033004650632543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9702522632088012401686781 3638445987033004650632543)
            ·
              refine ⟨5457668980549506975948815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638445987033004650632543 5457668980549506975948815)
              ·
                refine ⟨8186503470824260463923223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457668980549506975948815 8186503470824260463923223)
                ·
                  refine ⟨12279755206236390695884835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8186503470824260463923223 12279755206236390695884835)
                  ·
                    refine ⟨18419632809354586043827253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12279755206236390695884835 18419632809354586043827253)
                    ·
                      refine ⟨1726840575876992441608805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18419632809354586043827253 1726840575876992441608805)
                      ·
                        rfl

theorem cell23_3363010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_3363010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363010 prefixEnd_3363010 := by exact prefixLift 3363010
  have htrace : WordTrace (prefixWord ++ tailWord_3363010) baseStart_3363010 baseEnd_3363010 := by
    simpa [prefixWord, tailWord_3363010, baseEnd_3363010] using wordTrace_append hprefix tailTrace_3363010
  have hstable : (prefixWord ++ tailWord_3363010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363010).length < 2 ^ (prefixWord ++ tailWord_3363010).sum := by decide
  have hdescent : baseEnd_3363010 < baseStart_3363010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363080 : List Nat := [2, 1, 3, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_3363080 : Nat := 118140960795 + 3363080 * 2 ^ 59
def prefixEnd_3363080 : Nat := 4983230072969 + 3 ^ 40 * 3363080 * 2
def baseEnd_3363080 : Nat := 1726876519522807167733483

theorem tailTrace_3363080 : CollatzResearch.WordTrace tailWord_3363080 prefixEnd_3363080 1726876519522807167733483 := by
  unfold tailWord_3363080
  simp only [CollatzResearch.WordTrace]
  refine ⟨61330802328071501590655347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81774403104095335454207129 61330802328071501590655347)
  ·
    refine ⟨91996203492107252385983021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61330802328071501590655347 91996203492107252385983021)
    ·
      refine ⟨34498576309540219644743633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91996203492107252385983021 34498576309540219644743633)
      ·
        refine ⟨25873932232155164733557725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34498576309540219644743633 25873932232155164733557725)
        ·
          refine ⟨9702724587058186775084147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25873932232155164733557725 9702724587058186775084147)
          ·
            refine ⟨14554086880587280162626221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702724587058186775084147 14554086880587280162626221)
            ·
              refine ⟨5457782580220230060984833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14554086880587280162626221 5457782580220230060984833)
              ·
                refine ⟨4093336935165172545738625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5457782580220230060984833 4093336935165172545738625)
                ·
                  refine ⟨3070002701373879409303969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4093336935165172545738625 3070002701373879409303969)
                  ·
                    refine ⟨2302502026030409556977977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3070002701373879409303969 2302502026030409556977977)
                    ·
                      refine ⟨1726876519522807167733483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2302502026030409556977977 1726876519522807167733483)
                      ·
                        rfl

theorem cell23_3363080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_3363080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363080 prefixEnd_3363080 := by exact prefixLift 3363080
  have htrace : WordTrace (prefixWord ++ tailWord_3363080) baseStart_3363080 baseEnd_3363080 := by
    simpa [prefixWord, tailWord_3363080, baseEnd_3363080] using wordTrace_append hprefix tailTrace_3363080
  have hstable : (prefixWord ++ tailWord_3363080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363080).length < 2 ^ (prefixWord ++ tailWord_3363080).sum := by decide
  have hdescent : baseEnd_3363080 < baseStart_3363080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363086 : List Nat := [4, 1, 1, 2, 1, 2, 1, 6, 5]
def baseStart_3363086 : Nat := 118140960795 + 3363086 * 2 ^ 59
def prefixEnd_3363086 : Nat := 4983230072969 + 3 ^ 40 * 3363086 * 2
def baseEnd_3363086 : Nat := 191875511156303793806495

theorem tailTrace_3363086 : CollatzResearch.WordTrace tailWord_3363086 prefixEnd_3363086 191875511156303793806495 := by
  unfold tailWord_3363086
  simp only [CollatzResearch.WordTrace]
  refine ⟨15332727936765158275753639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81774548996080844137352741 15332727936765158275753639)
  ·
    refine ⟨22999091905147737413630459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15332727936765158275753639 22999091905147737413630459)
    ·
      refine ⟨34498637857721606120445689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22999091905147737413630459 34498637857721606120445689)
      ·
        refine ⟨25873978393291204590334267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34498637857721606120445689 25873978393291204590334267)
        ·
          refine ⟨38810967589936806885501401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25873978393291204590334267 38810967589936806885501401)
          ·
            refine ⟨29108225692452605164126051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38810967589936806885501401 29108225692452605164126051)
            ·
              refine ⟨43662338538678907746189077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29108225692452605164126051 43662338538678907746189077)
              ·
                refine ⟨2046672119000573800602613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43662338538678907746189077 2046672119000573800602613)
                ·
                  refine ⟨191875511156303793806495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2046672119000573800602613 191875511156303793806495)
                  ·
                    rfl

theorem cell23_3363086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 6, 5].length) (baseStart_3363086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363086 prefixEnd_3363086 := by exact prefixLift 3363086
  have htrace : WordTrace (prefixWord ++ tailWord_3363086) baseStart_3363086 baseEnd_3363086 := by
    simpa [prefixWord, tailWord_3363086, baseEnd_3363086] using wordTrace_append hprefix tailTrace_3363086
  have hstable : (prefixWord ++ tailWord_3363086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363086).length < 2 ^ (prefixWord ++ tailWord_3363086).sum := by decide
  have hdescent : baseEnd_3363086 < baseStart_3363086 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363119 : List Nat := [1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 4]
def baseStart_3363119 : Nat := 118140960795 + 3363119 * 2 ^ 59
def prefixEnd_3363119 : Nat := 4983230072969 + 3 ^ 40 * 3363119 * 2
def baseEnd_3363119 : Nat := 1726896545268332515145803

theorem tailTrace_3363119 : CollatzResearch.WordTrace tailWord_3363119 prefixEnd_3363119 1726896545268332515145803 := by
  unfold tailWord_3363119
  simp only [CollatzResearch.WordTrace]
  refine ⟨122663027103001712841980411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81775351402001141894653607 122663027103001712841980411)
  ·
    refine ⟨183994540654502569262970617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122663027103001712841980411 183994540654502569262970617)
    ·
      refine ⟨137995905490876926947227963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183994540654502569262970617 137995905490876926947227963)
      ·
        refine ⟨206993858236315390420841945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137995905490876926947227963 206993858236315390420841945)
        ·
          refine ⟨155245393677236542815631459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206993858236315390420841945 155245393677236542815631459)
          ·
            refine ⟨232868090515854814223447189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155245393677236542815631459 232868090515854814223447189)
            ·
              refine ⟨10915691742930694416724087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 232868090515854814223447189 10915691742930694416724087)
              ·
                refine ⟨16373537614396041625086131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10915691742930694416724087 16373537614396041625086131)
                ·
                  refine ⟨24560306421594062437629197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16373537614396041625086131 24560306421594062437629197)
                  ·
                    refine ⟨9210114908097773414110949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24560306421594062437629197 9210114908097773414110949)
                    ·
                      refine ⟨1726896545268332515145803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9210114908097773414110949 1726896545268332515145803)
                      ·
                        rfl

theorem cell23_3363119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 4].length) (baseStart_3363119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363119 prefixEnd_3363119 := by exact prefixLift 3363119
  have htrace : WordTrace (prefixWord ++ tailWord_3363119) baseStart_3363119 baseEnd_3363119 := by
    simpa [prefixWord, tailWord_3363119, baseEnd_3363119] using wordTrace_append hprefix tailTrace_3363119
  have hstable : (prefixWord ++ tailWord_3363119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363119).length < 2 ^ (prefixWord ++ tailWord_3363119).sum := by decide
  have hdescent : baseEnd_3363119 < baseStart_3363119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363136 : List Nat := [2, 1, 1, 2, 2, 1, 2, 4, 2, 4, 2]
def baseStart_3363136 : Nat := 118140960795 + 3363136 * 2 ^ 59
def prefixEnd_3363136 : Nat := 4983230072969 + 3 ^ 40 * 3363136 * 2
def baseEnd_3363136 : Nat := 1726905274439458948633225

theorem tailTrace_3363136 : CollatzResearch.WordTrace tailWord_3363136 prefixEnd_3363136 1726905274439458948633225 := by
  unfold tailWord_3363136
  simp only [CollatzResearch.WordTrace]
  refine ⟨61331823571970062372674631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81775764762626749830232841 61331823571970062372674631)
  ·
    refine ⟨91997735357955093559011947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61331823571970062372674631 91997735357955093559011947)
    ·
      refine ⟨137996603036932640338517921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91997735357955093559011947 137996603036932640338517921)
      ·
        refine ⟨103497452277699480253888441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137996603036932640338517921 103497452277699480253888441)
        ·
          refine ⟨77623089208274610190416331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103497452277699480253888441 77623089208274610190416331)
          ·
            refine ⟨116434633812411915285624497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77623089208274610190416331 116434633812411915285624497)
            ·
              refine ⟨87325975359308936464218373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116434633812411915285624497 87325975359308936464218373)
              ·
                refine ⟨16373620379870425587040945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87325975359308936464218373 16373620379870425587040945)
                ·
                  refine ⟨12280215284902819190280709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16373620379870425587040945 12280215284902819190280709)
                  ·
                    refine ⟨2302540365919278598177633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12280215284902819190280709 2302540365919278598177633)
                    ·
                      refine ⟨1726905274439458948633225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2302540365919278598177633 1726905274439458948633225)
                      ·
                        rfl

theorem cell23_3363136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_3363136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363136 prefixEnd_3363136 := by exact prefixLift 3363136
  have htrace : WordTrace (prefixWord ++ tailWord_3363136) baseStart_3363136 baseEnd_3363136 := by
    simpa [prefixWord, tailWord_3363136, baseEnd_3363136] using wordTrace_append hprefix tailTrace_3363136
  have hstable : (prefixWord ++ tailWord_3363136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363136).length < 2 ^ (prefixWord ++ tailWord_3363136).sum := by decide
  have hdescent : baseEnd_3363136 < baseStart_3363136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363173 : List Nat := [1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 3]
def baseStart_3363173 : Nat := 118140960795 + 3363173 * 2 ^ 59
def prefixEnd_3363173 : Nat := 4983230072969 + 3 ^ 40 * 3363173 * 2
def baseEnd_3363173 : Nat := 1726924273223675303870555

theorem tailTrace_3363173 : CollatzResearch.WordTrace tailWord_3363173 prefixEnd_3363173 1726924273223675303870555 := by
  unfold tailWord_3363173
  simp only [CollatzResearch.WordTrace]
  refine ⟨122664996644806080064446173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81776664429870720042964115 122664996644806080064446173)
  ·
    refine ⟨45999373741802280024167315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122664996644806080064446173 45999373741802280024167315)
    ·
      refine ⟨68999060612703420036250973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45999373741802280024167315 68999060612703420036250973)
      ·
        refine ⟨25874647729763782513594115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68999060612703420036250973 25874647729763782513594115)
        ·
          refine ⟨38811971594645673770391173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25874647729763782513594115 38811971594645673770391173)
          ·
            refine ⟨7277244673996063831948345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38811971594645673770391173 7277244673996063831948345)
            ·
              refine ⟨5457933505497047873961259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7277244673996063831948345 5457933505497047873961259)
              ·
                refine ⟨8186900258245571810941889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5457933505497047873961259 8186900258245571810941889)
                ·
                  refine ⟨6140175193684178858206417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8186900258245571810941889 6140175193684178858206417)
                  ·
                    refine ⟨4605131395263134143654813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140175193684178858206417 4605131395263134143654813)
                    ·
                      refine ⟨1726924273223675303870555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4605131395263134143654813 1726924273223675303870555)
                      ·
                        rfl

theorem cell23_3363173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 2, 1, 2, 2, 3].length) (baseStart_3363173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363173 prefixEnd_3363173 := by exact prefixLift 3363173
  have htrace : WordTrace (prefixWord ++ tailWord_3363173) baseStart_3363173 baseEnd_3363173 := by
    simpa [prefixWord, tailWord_3363173, baseEnd_3363173] using wordTrace_append hprefix tailTrace_3363173
  have hstable : (prefixWord ++ tailWord_3363173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363173).length < 2 ^ (prefixWord ++ tailWord_3363173).sum := by decide
  have hdescent : baseEnd_3363173 < baseStart_3363173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363197 : List Nat := [1, 4, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_3363197 : Nat := 118140960795 + 3363197 * 2 ^ 59
def prefixEnd_3363197 : Nat := 4983230072969 + 3 ^ 40 * 3363197 * 2
def baseEnd_3363197 : Nat := 575645532253127736656815

theorem tailTrace_3363197 : CollatzResearch.WordTrace tailWord_3363197 prefixEnd_3363197 575645532253127736656815 := by
  unfold tailWord_3363197
  simp only [CollatzResearch.WordTrace]
  refine ⟨122665871996719132163319845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81777247997812754775546563 122665871996719132163319845)
  ·
    refine ⟨22999850999384837280622471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122665871996719132163319845 22999850999384837280622471)
    ·
      refine ⟨34499776499077255920933707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22999850999384837280622471 34499776499077255920933707)
      ·
        refine ⟨51749664748615883881400561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34499776499077255920933707 51749664748615883881400561)
        ·
          refine ⟨38812248561461912911050421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51749664748615883881400561 38812248561461912911050421)
          ·
            refine ⟨3638648302637054335410977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38812248561461912911050421 3638648302637054335410977)
            ·
              refine ⟨2728986226977790751558233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3638648302637054335410977 2728986226977790751558233)
              ·
                refine ⟨2046739670233343063668675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728986226977790751558233 2046739670233343063668675)
                ·
                  refine ⟨3070109505350014595503013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046739670233343063668675 3070109505350014595503013)
                  ·
                    refine ⟨575645532253127736656815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3070109505350014595503013 575645532253127736656815)
                    ·
                      rfl

theorem cell23_3363197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_3363197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363197 prefixEnd_3363197 := by exact prefixLift 3363197
  have htrace : WordTrace (prefixWord ++ tailWord_3363197) baseStart_3363197 baseEnd_3363197 := by
    simpa [prefixWord, tailWord_3363197, baseEnd_3363197] using wordTrace_append hprefix tailTrace_3363197
  have hstable : (prefixWord ++ tailWord_3363197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363197).length < 2 ^ (prefixWord ++ tailWord_3363197).sum := by decide
  have hdescent : baseEnd_3363197 < baseStart_3363197 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363236 : List Nat := [2, 3, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_3363236 : Nat := 118140960795 + 3363236 * 2 ^ 59
def prefixEnd_3363236 : Nat := 4983230072969 + 3 ^ 40 * 3363236 * 2
def baseEnd_3363236 : Nat := 575652207501636185794255

theorem tailTrace_3363236 : CollatzResearch.WordTrace tailWord_3363236 prefixEnd_3363236 575652207501636185794255 := by
  unfold tailWord_3363236
  simp only [CollatzResearch.WordTrace]
  refine ⟨61333647221788920911994781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81778196295718561215993041 61333647221788920911994781)
  ·
    refine ⟨23000117708170845341998043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61333647221788920911994781 23000117708170845341998043)
    ·
      refine ⟨34500176562256268012997065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23000117708170845341998043 34500176562256268012997065)
      ·
        refine ⟨25875132421692201009747799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34500176562256268012997065 25875132421692201009747799)
        ·
          refine ⟨38812698632538301514621699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25875132421692201009747799 38812698632538301514621699)
          ·
            refine ⟨58219047948807452271932549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38812698632538301514621699 58219047948807452271932549)
            ·
              refine ⟨10916071490401397300987353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58219047948807452271932549 10916071490401397300987353)
              ·
                refine ⟨8187053617801047975740515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10916071490401397300987353 8187053617801047975740515)
                ·
                  refine ⟨12280580426701571963610773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8187053617801047975740515 12280580426701571963610773)
                  ·
                    refine ⟨575652207501636185794255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12280580426701571963610773 575652207501636185794255)
                    ·
                      rfl

theorem cell23_3363236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_3363236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363236 prefixEnd_3363236 := by exact prefixLift 3363236
  have htrace : WordTrace (prefixWord ++ tailWord_3363236) baseStart_3363236 baseEnd_3363236 := by
    simpa [prefixWord, tailWord_3363236, baseEnd_3363236] using wordTrace_append hprefix tailTrace_3363236
  have hstable : (prefixWord ++ tailWord_3363236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363236).length < 2 ^ (prefixWord ++ tailWord_3363236).sum := by decide
  have hdescent : baseEnd_3363236 < baseStart_3363236 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363240 : List Nat := [2, 1, 6, 1, 1, 2, 1, 3, 1, 5]
def baseStart_3363240 : Nat := 118140960795 + 3363240 * 2 ^ 59
def prefixEnd_3363240 : Nat := 4983230072969 + 3 ^ 40 * 3363240 * 2
def baseEnd_3363240 : Nat := 575652892142508847244249

theorem tailTrace_3363240 : CollatzResearch.WordTrace tailWord_3363240 prefixEnd_3363240 575652892142508847244249 := by
  unfold tailWord_3363240
  simp only [CollatzResearch.WordTrace]
  refine ⟨61333720167781675253567587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81778293557042233671423449 61333720167781675253567587)
  ·
    refine ⟨92000580251672512880351381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61333720167781675253567587 92000580251672512880351381)
    ·
      refine ⟨4312527199297149041266471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92000580251672512880351381 4312527199297149041266471)
      ·
        refine ⟨6468790798945723561899707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312527199297149041266471 6468790798945723561899707)
        ·
          refine ⟨9703186198418585342849561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6468790798945723561899707 9703186198418585342849561)
          ·
            refine ⟨7277389648813939007137171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9703186198418585342849561 7277389648813939007137171)
            ·
              refine ⟨10916084473220908510705757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7277389648813939007137171 10916084473220908510705757)
              ·
                refine ⟨4093531677457840691514659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10916084473220908510705757 4093531677457840691514659)
                ·
                  refine ⟨6140297516186761037271989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4093531677457840691514659 6140297516186761037271989)
                  ·
                    refine ⟨575652892142508847244249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6140297516186761037271989 575652892142508847244249)
                    ·
                      rfl

theorem cell23_3363240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_3363240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363240 prefixEnd_3363240 := by exact prefixLift 3363240
  have htrace : WordTrace (prefixWord ++ tailWord_3363240) baseStart_3363240 baseEnd_3363240 := by
    simpa [prefixWord, tailWord_3363240, baseEnd_3363240] using wordTrace_append hprefix tailTrace_3363240
  have hstable : (prefixWord ++ tailWord_3363240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363240).length < 2 ^ (prefixWord ++ tailWord_3363240).sum := by decide
  have hdescent : baseEnd_3363240 < baseStart_3363240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363293 : List Nat := [1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3363293 : Nat := 118140960795 + 3363293 * 2 ^ 59
def prefixEnd_3363293 : Nat := 4983230072969 + 3 ^ 40 * 3363293 * 2
def baseEnd_3363293 : Nat := 1726985890902214834370003

theorem tailTrace_3363293 : CollatzResearch.WordTrace tailWord_3363293 prefixEnd_3363293 1726985890902214834370003 := by
  unfold tailWord_3363293
  simp only [CollatzResearch.WordTrace]
  refine ⟨122669373404371340558814533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81779582269580893705876355 122669373404371340558814533)
  ·
    refine ⟨23000507513319626354777725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122669373404371340558814533 23000507513319626354777725)
    ·
      refine ⟨8625190317494859883041647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23000507513319626354777725 8625190317494859883041647)
      ·
        refine ⟨12937785476242289824562471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8625190317494859883041647 12937785476242289824562471)
        ·
          refine ⟨19406678214363434736843707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12937785476242289824562471 19406678214363434736843707)
          ·
            refine ⟨29110017321545152105265561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19406678214363434736843707 29110017321545152105265561)
            ·
              refine ⟨21832512991158864078949171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29110017321545152105265561 21832512991158864078949171)
              ·
                refine ⟨32748769486738296118423757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21832512991158864078949171 32748769486738296118423757)
                ·
                  refine ⟨12280788557526861044408909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32748769486738296118423757 12280788557526861044408909)
                  ·
                    refine ⟨4605295709072572891653341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12280788557526861044408909 4605295709072572891653341)
                    ·
                      refine ⟨1726985890902214834370003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4605295709072572891653341 1726985890902214834370003)
                      ·
                        rfl

theorem cell23_3363293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3363293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363293 prefixEnd_3363293 := by exact prefixLift 3363293
  have htrace : WordTrace (prefixWord ++ tailWord_3363293) baseStart_3363293 baseEnd_3363293 := by
    simpa [prefixWord, tailWord_3363293, baseEnd_3363293] using wordTrace_append hprefix tailTrace_3363293
  have hstable : (prefixWord ++ tailWord_3363293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363293).length < 2 ^ (prefixWord ++ tailWord_3363293).sum := by decide
  have hdescent : baseEnd_3363293 < baseStart_3363293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363310 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3]
def baseStart_3363310 : Nat := 118140960795 + 3363310 * 2 ^ 59
def prefixEnd_3363310 : Nat := 4983230072969 + 3 ^ 40 * 3363310 * 2
def baseEnd_3363310 : Nat := 1726994620073341267857425

theorem tailTrace_3363310 : CollatzResearch.WordTrace tailWord_3363310 prefixEnd_3363310 1726994620073341267857425 := by
  unfold tailWord_3363310
  simp only [CollatzResearch.WordTrace]
  refine ⟨15333749180663719057772923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81779995630206501641455589 15333749180663719057772923)
  ·
    refine ⟨23000623770995578586659385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15333749180663719057772923 23000623770995578586659385)
    ·
      refine ⟨17250467828246683939994539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23000623770995578586659385 17250467828246683939994539)
      ·
        refine ⟨25875701742370025909991809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17250467828246683939994539 25875701742370025909991809)
        ·
          refine ⟨19406776306777519432493857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25875701742370025909991809 19406776306777519432493857)
          ·
            refine ⟨14555082230083139574370393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19406776306777519432493857 14555082230083139574370393)
            ·
              refine ⟨10916311672562354680777795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14555082230083139574370393 10916311672562354680777795)
              ·
                refine ⟨16374467508843532021166693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10916311672562354680777795 16374467508843532021166693)
                ·
                  refine ⟨3070212657908162253968755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16374467508843532021166693 3070212657908162253968755)
                  ·
                    refine ⟨4605318986862243380953133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3070212657908162253968755 4605318986862243380953133)
                    ·
                      refine ⟨1726994620073341267857425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4605318986862243380953133 1726994620073341267857425)
                      ·
                        rfl

theorem cell23_3363310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_3363310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363310 prefixEnd_3363310 := by exact prefixLift 3363310
  have htrace : WordTrace (prefixWord ++ tailWord_3363310) baseStart_3363310 baseEnd_3363310 := by
    simpa [prefixWord, tailWord_3363310, baseEnd_3363310] using wordTrace_append hprefix tailTrace_3363310
  have hstable : (prefixWord ++ tailWord_3363310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363310).length < 2 ^ (prefixWord ++ tailWord_3363310).sum := by decide
  have hdescent : baseEnd_3363310 < baseStart_3363310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363383 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 3]
def baseStart_3363383 : Nat := 118140960795 + 3363383 * 2 ^ 59
def prefixEnd_3363383 : Nat := 4983230072969 + 3 ^ 40 * 3363383 * 2
def baseEnd_3363383 : Nat := 1727032104161119482244589

theorem tailTrace_3363383 : CollatzResearch.WordTrace tailWord_3363383 prefixEnd_3363383 1727032104161119482244589 := by
  unfold tailWord_3363383
  simp only [CollatzResearch.WordTrace]
  refine ⟨122672655974045285929590803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81781770649363523953060535 122672655974045285929590803)
  ·
    refine ⟨184008983961067928894386205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122672655974045285929590803 184008983961067928894386205)
    ·
      refine ⟨69003368985400473335394827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184008983961067928894386205 69003368985400473335394827)
      ·
        refine ⟨103505053478100710003092241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69003368985400473335394827 103505053478100710003092241)
        ·
          refine ⟨77628790108575532502319181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103505053478100710003092241 77628790108575532502319181)
          ·
            refine ⟨29110796290715824688369693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77628790108575532502319181 29110796290715824688369693)
            ·
              refine ⟨10916548609018434258138635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29110796290715824688369693 10916548609018434258138635)
              ·
                refine ⟨16374822913527651387207953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10916548609018434258138635 16374822913527651387207953)
                ·
                  refine ⟨12281117185145738540405965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16374822913527651387207953 12281117185145738540405965)
                  ·
                    refine ⟨4605418944429651952652237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12281117185145738540405965 4605418944429651952652237)
                    ·
                      refine ⟨1727032104161119482244589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4605418944429651952652237 1727032104161119482244589)
                      ·
                        rfl

theorem cell23_3363383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_3363383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363383 prefixEnd_3363383 := by exact prefixLift 3363383
  have htrace : WordTrace (prefixWord ++ tailWord_3363383) baseStart_3363383 baseEnd_3363383 := by
    simpa [prefixWord, tailWord_3363383, baseEnd_3363383] using wordTrace_append hprefix tailTrace_3363383
  have hstable : (prefixWord ++ tailWord_3363383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363383).length < 2 ^ (prefixWord ++ tailWord_3363383).sum := by decide
  have hdescent : baseEnd_3363383 < baseStart_3363383 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363403 : List Nat := [1, 1, 1, 1, 3, 1, 7, 1, 2, 5]
def baseStart_3363403 : Nat := 118140960795 + 3363403 * 2 ^ 59
def prefixEnd_3363403 : Nat := 4983230072969 + 3 ^ 40 * 3363403 * 2
def baseEnd_3363403 : Nat := 575680791258069801331499

theorem tailTrace_3363403 : CollatzResearch.WordTrace tailWord_3363403 prefixEnd_3363403 575680791258069801331499 := by
  unfold tailWord_3363403
  simp only [CollatzResearch.WordTrace]
  refine ⟨122673385433972829345318863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81782256955981886230212575 122673385433972829345318863)
  ·
    refine ⟨184010078150959244017978295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122673385433972829345318863 184010078150959244017978295)
    ·
      refine ⟨276015117226438866026967443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184010078150959244017978295 276015117226438866026967443)
      ·
        refine ⟨414022675839658299040451165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276015117226438866026967443 414022675839658299040451165)
        ·
          refine ⟨155258503439871862140169187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 414022675839658299040451165 155258503439871862140169187)
          ·
            refine ⟨232887755159807793210253781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155258503439871862140169187 232887755159807793210253781)
            ·
              refine ⟨5458306761557995153365323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 232887755159807793210253781 5458306761557995153365323)
              ·
                refine ⟨8187460142336992730047985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5458306761557995153365323 8187460142336992730047985)
                ·
                  refine ⟨6140595106752744547535989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8187460142336992730047985 6140595106752744547535989)
                  ·
                    refine ⟨575680791258069801331499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6140595106752744547535989 575680791258069801331499)
                    ·
                      rfl

theorem cell23_3363403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 5].length) (baseStart_3363403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363403 prefixEnd_3363403 := by exact prefixLift 3363403
  have htrace : WordTrace (prefixWord ++ tailWord_3363403) baseStart_3363403 baseEnd_3363403 := by
    simpa [prefixWord, tailWord_3363403, baseEnd_3363403] using wordTrace_append hprefix tailTrace_3363403
  have hstable : (prefixWord ++ tailWord_3363403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363403).length < 2 ^ (prefixWord ++ tailWord_3363403).sum := by decide
  have hdescent : baseEnd_3363403 < baseStart_3363403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363423 : List Nat := [1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 4]
def baseStart_3363423 : Nat := 118140960795 + 3363423 * 2 ^ 59
def prefixEnd_3363423 : Nat := 4983230072969 + 3 ^ 40 * 3363423 * 2
def baseEnd_3363423 : Nat := 1727052643387299325744405

theorem tailTrace_3363423 : CollatzResearch.WordTrace tailWord_3363423 prefixEnd_3363423 1727052643387299325744405 := by
  unfold tailWord_3363423
  simp only [CollatzResearch.WordTrace]
  refine ⟨122674114893900372761046923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81782743262600248507364615 122674114893900372761046923)
  ·
    refine ⟨184011172340850559141570385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122674114893900372761046923 184011172340850559141570385)
    ·
      refine ⟨138008379255637919356177789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 184011172340850559141570385 138008379255637919356177789)
      ·
        refine ⟨51753142220864219758566671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138008379255637919356177789 51753142220864219758566671)
        ·
          refine ⟨77629713331296329637850007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51753142220864219758566671 77629713331296329637850007)
          ·
            refine ⟨116444569996944494456775011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77629713331296329637850007 116444569996944494456775011)
            ·
              refine ⟨174666854995416741685162517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116444569996944494456775011 174666854995416741685162517)
              ·
                refine ⟨8187508827910159766491993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 174666854995416741685162517 8187508827910159766491993)
                ·
                  refine ⟨6140631620932619824868995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8187508827910159766491993 6140631620932619824868995)
                  ·
                    refine ⟨9210947431398929737303493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6140631620932619824868995 9210947431398929737303493)
                    ·
                      refine ⟨1727052643387299325744405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9210947431398929737303493 1727052643387299325744405)
                      ·
                        rfl

theorem cell23_3363423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 1, 4].length) (baseStart_3363423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363423 prefixEnd_3363423 := by exact prefixLift 3363423
  have htrace : WordTrace (prefixWord ++ tailWord_3363423) baseStart_3363423 baseEnd_3363423 := by
    simpa [prefixWord, tailWord_3363423, baseEnd_3363423] using wordTrace_append hprefix tailTrace_3363423
  have hstable : (prefixWord ++ tailWord_3363423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363423).length < 2 ^ (prefixWord ++ tailWord_3363423).sum := by decide
  have hdescent : baseEnd_3363423 < baseStart_3363423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363443 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 3]
def baseStart_3363443 : Nat := 118140960795 + 3363443 * 2 ^ 59
def prefixEnd_3363443 : Nat := 4983230072969 + 3 ^ 40 * 3363443 * 2
def baseEnd_3363443 : Nat := 1727062913000389247494313

theorem tailTrace_3363443 : CollatzResearch.WordTrace tailWord_3363443 prefixEnd_3363443 1727062913000389247494313 := by
  unfold tailWord_3363443
  simp only [CollatzResearch.WordTrace]
  refine ⟨122674844353827916176774983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81783229569218610784516655 122674844353827916176774983)
  ·
    refine ⟨184012266530741874265162475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122674844353827916176774983 184012266530741874265162475)
    ·
      refine ⟨276018399796112811397743713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184012266530741874265162475 276018399796112811397743713)
      ·
        refine ⟨207013799847084608548307785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276018399796112811397743713 207013799847084608548307785)
        ·
          refine ⟨155260349885313456411230839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207013799847084608548307785 155260349885313456411230839)
          ·
            refine ⟨232890524827970184616846259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155260349885313456411230839 232890524827970184616846259)
            ·
              refine ⟨349335787241955276925269389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232890524827970184616846259 349335787241955276925269389)
              ·
                refine ⟨131000920215733228846976021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 349335787241955276925269389 131000920215733228846976021)
                ·
                  refine ⟨6140668135112495102202001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 131000920215733228846976021 6140668135112495102202001)
                  ·
                    refine ⟨4605501101334371326651501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6140668135112495102202001 4605501101334371326651501)
                    ·
                      refine ⟨1727062913000389247494313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4605501101334371326651501 1727062913000389247494313)
                      ·
                        rfl

theorem cell23_3363443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 6, 2, 3].length) (baseStart_3363443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363443 prefixEnd_3363443 := by exact prefixLift 3363443
  have htrace : WordTrace (prefixWord ++ tailWord_3363443) baseStart_3363443 baseEnd_3363443 := by
    simpa [prefixWord, tailWord_3363443, baseEnd_3363443] using wordTrace_append hprefix tailTrace_3363443
  have hstable : (prefixWord ++ tailWord_3363443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363443).length < 2 ^ (prefixWord ++ tailWord_3363443).sum := by decide
  have hdescent : baseEnd_3363443 < baseStart_3363443 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363458 : List Nat := [3, 4, 3, 1, 1, 2, 1, 3, 5]
def baseStart_3363458 : Nat := 118140960795 + 3363458 * 2 ^ 59
def prefixEnd_3363458 : Nat := 4983230072969 + 3 ^ 40 * 3363458 * 2
def baseEnd_3363458 : Nat := 191896735023356298756305

theorem tailTrace_3363458 : CollatzResearch.WordTrace tailWord_3363458 prefixEnd_3363458 191896735023356298756305 := by
  unfold tailWord_3363458
  simp only [CollatzResearch.WordTrace]
  refine ⟨30668847862193393434642757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81783594299182382492380685 30668847862193393434642757)
  ·
    refine ⟨5750408974161261268995517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30668847862193393434642757 5750408974161261268995517)
    ·
      refine ⟨2156403365310472975873319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5750408974161261268995517 2156403365310472975873319)
      ·
        refine ⟨3234605047965709463809979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156403365310472975873319 3234605047965709463809979)
        ·
          refine ⟨4851907571948564195714969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234605047965709463809979 4851907571948564195714969)
          ·
            refine ⟨3638930678961423146786227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4851907571948564195714969 3638930678961423146786227)
            ·
              refine ⟨5458396018442134720179341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638930678961423146786227 5458396018442134720179341)
              ·
                refine ⟨2046898506915800520067253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5458396018442134720179341 2046898506915800520067253)
                ·
                  refine ⟨191896735023356298756305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2046898506915800520067253 191896735023356298756305)
                  ·
                    rfl

theorem cell23_3363458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 2, 1, 3, 5].length) (baseStart_3363458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363458 prefixEnd_3363458 := by exact prefixLift 3363458
  have htrace : WordTrace (prefixWord ++ tailWord_3363458) baseStart_3363458 baseEnd_3363458 := by
    simpa [prefixWord, tailWord_3363458, baseEnd_3363458] using wordTrace_append hprefix tailTrace_3363458
  have hstable : (prefixWord ++ tailWord_3363458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363458).length < 2 ^ (prefixWord ++ tailWord_3363458).sum := by decide
  have hdescent : baseEnd_3363458 < baseStart_3363458 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363460 : List Nat := [2, 3, 2, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_3363460 : Nat := 118140960795 + 3363460 * 2 ^ 59
def prefixEnd_3363460 : Nat := 4983230072969 + 3 ^ 40 * 3363460 * 2
def baseEnd_3363460 : Nat := 1727071642171515680981735

theorem tailTrace_3363460 : CollatzResearch.WordTrace tailWord_3363460 prefixEnd_3363460 1727071642171515680981735 := by
  unfold tailWord_3363460
  simp only [CollatzResearch.WordTrace]
  refine ⟨61337732197383164040071917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81783642929844218720095889 61337732197383164040071917)
  ·
    refine ⟨23001649574018686515026969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61337732197383164040071917 23001649574018686515026969)
    ·
      refine ⟨17251237180514014886270227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23001649574018686515026969 17251237180514014886270227)
      ·
        refine ⟨25876855770771022329405341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17251237180514014886270227 25876855770771022329405341)
        ·
          refine ⟨9703820914039133373527003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25876855770771022329405341 9703820914039133373527003)
          ·
            refine ⟨14555731371058700060290505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9703820914039133373527003 14555731371058700060290505)
            ·
              refine ⟨10916798528294025045217879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14555731371058700060290505 10916798528294025045217879)
              ·
                refine ⟨16375197792441037567826819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10916798528294025045217879 16375197792441037567826819)
                ·
                  refine ⟨24562796688661556351740229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16375197792441037567826819 24562796688661556351740229)
                  ·
                    refine ⟨4605524379124041815951293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24562796688661556351740229 4605524379124041815951293)
                    ·
                      refine ⟨1727071642171515680981735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4605524379124041815951293 1727071642171515680981735)
                      ·
                        rfl

theorem cell23_3363460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_3363460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363460 prefixEnd_3363460 := by exact prefixLift 3363460
  have htrace : WordTrace (prefixWord ++ tailWord_3363460) baseStart_3363460 baseEnd_3363460 := by
    simpa [prefixWord, tailWord_3363460, baseEnd_3363460] using wordTrace_append hprefix tailTrace_3363460
  have hstable : (prefixWord ++ tailWord_3363460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363460).length < 2 ^ (prefixWord ++ tailWord_3363460).sum := by decide
  have hdescent : baseEnd_3363460 < baseStart_3363460 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363493 : List Nat := [1, 3, 1, 2, 1, 2, 1, 4, 3, 5]
def baseStart_3363493 : Nat := 118140960795 + 3363493 * 2 ^ 59
def prefixEnd_3363493 : Nat := 4983230072969 + 3 ^ 40 * 3363493 * 2
def baseEnd_3363493 : Nat := 575696195677704683956361

theorem tailTrace_3363493 : CollatzResearch.WordTrace tailWord_3363493 prefixEnd_3363493 575696195677704683956361 := by
  unfold tailWord_3363493
  simp only [CollatzResearch.WordTrace]
  refine ⟨122676668003646774716095133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81784445335764516477396755 122676668003646774716095133)
  ·
    refine ⟨46003750501367540518535675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122676668003646774716095133 46003750501367540518535675)
    ·
      refine ⟨69005625752051310777803513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46003750501367540518535675 69005625752051310777803513)
      ·
        refine ⟨51754219314038483083352635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69005625752051310777803513 51754219314038483083352635)
        ·
          refine ⟨77631328971057724625028953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51754219314038483083352635 77631328971057724625028953)
          ·
            refine ⟨58223496728293293468771715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77631328971057724625028953 58223496728293293468771715)
            ·
              refine ⟨87335245092439940203157573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58223496728293293468771715 87335245092439940203157573)
              ·
                refine ⟨16375358454832488788092045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87335245092439940203157573 16375358454832488788092045)
                ·
                  refine ⟨6140759420562183295534517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16375358454832488788092045 6140759420562183295534517)
                  ·
                    refine ⟨575696195677704683956361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6140759420562183295534517 575696195677704683956361)
                    ·
                      rfl

theorem cell23_3363493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 5].length) (baseStart_3363493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363493 prefixEnd_3363493 := by exact prefixLift 3363493
  have htrace : WordTrace (prefixWord ++ tailWord_3363493) baseStart_3363493 baseEnd_3363493 := by
    simpa [prefixWord, tailWord_3363493, baseEnd_3363493] using wordTrace_append hprefix tailTrace_3363493
  have hstable : (prefixWord ++ tailWord_3363493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363493).length < 2 ^ (prefixWord ++ tailWord_3363493).sum := by decide
  have hdescent : baseEnd_3363493 < baseStart_3363493 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363517 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 2, 3, 2]
def baseStart_3363517 : Nat := 118140960795 + 3363517 * 2 ^ 59
def prefixEnd_3363517 : Nat := 4983230072969 + 3 ^ 40 * 3363517 * 2
def baseEnd_3363517 : Nat := 1727100910568821957968973

theorem tailTrace_3363517 : CollatzResearch.WordTrace tailWord_3363517 prefixEnd_3363517 1727100910568821957968973 := by
  unfold tailWord_3363517
  simp only [CollatzResearch.WordTrace]
  refine ⟨122677543355559826814968805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81785028903706551209979203 122677543355559826814968805)
  ·
    refine ⟨23002039379167467527806651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122677543355559826814968805 23002039379167467527806651)
    ·
      refine ⟨34503059068751201291709977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23002039379167467527806651 34503059068751201291709977)
      ·
        refine ⟨25877294301563400968782483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34503059068751201291709977 25877294301563400968782483)
        ·
          refine ⟨38815941452345101453173725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25877294301563400968782483 38815941452345101453173725)
          ·
            refine ⟨14555978044629413044940147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38815941452345101453173725 14555978044629413044940147)
            ·
              refine ⟨21833967066944119567410221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14555978044629413044940147 21833967066944119567410221)
              ·
                refine ⟨8187737650104044837778833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21833967066944119567410221 8187737650104044837778833)
                ·
                  refine ⟨6140803237578033628334125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8187737650104044837778833 6140803237578033628334125)
                  ·
                    refine ⟨2302801214091762610625297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6140803237578033628334125 2302801214091762610625297)
                    ·
                      refine ⟨1727100910568821957968973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2302801214091762610625297 1727100910568821957968973)
                      ·
                        rfl

theorem cell23_3363517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_3363517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363517 prefixEnd_3363517 := by exact prefixLift 3363517
  have htrace : WordTrace (prefixWord ++ tailWord_3363517) baseStart_3363517 baseEnd_3363517 := by
    simpa [prefixWord, tailWord_3363517, baseEnd_3363517] using wordTrace_append hprefix tailTrace_3363517
  have hstable : (prefixWord ++ tailWord_3363517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363517).length < 2 ^ (prefixWord ++ tailWord_3363517).sum := by decide
  have hdescent : baseEnd_3363517 < baseStart_3363517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363557 : List Nat := [1, 3, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_3363557 : Nat := 118140960795 + 3363557 * 2 ^ 59
def prefixEnd_3363557 : Nat := 4983230072969 + 3 ^ 40 * 3363557 * 2
def baseEnd_3363557 : Nat := 575707149931667267156263

theorem tailTrace_3363557 : CollatzResearch.WordTrace tailWord_3363557 prefixEnd_3363557 575707149931667267156263 := by
  unfold tailWord_3363557
  simp only [CollatzResearch.WordTrace]
  refine ⟨122679002275414913646424925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81786001516943275764283283 122679002275414913646424925)
  ·
    refine ⟨46004625853280592617409347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122679002275414913646424925 46004625853280592617409347)
    ·
      refine ⟨69006938779920888926114021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46004625853280592617409347 69006938779920888926114021)
      ·
        refine ⟨12938801021235166673646379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69006938779920888926114021 12938801021235166673646379)
        ·
          refine ⟨19408201531852750010469569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12938801021235166673646379 19408201531852750010469569)
          ·
            refine ⟨14556151148889562507852177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19408201531852750010469569 14556151148889562507852177)
            ·
              refine ⟨10917113361667171880889133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14556151148889562507852177 10917113361667171880889133)
              ·
                refine ⟨4093917510625189455333425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10917113361667171880889133 4093917510625189455333425)
                ·
                  refine ⟨3070438132968892091500069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4093917510625189455333425 3070438132968892091500069)
                  ·
                    refine ⟨575707149931667267156263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3070438132968892091500069 575707149931667267156263)
                    ·
                      rfl

theorem cell23_3363557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_3363557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363557 prefixEnd_3363557 := by exact prefixLift 3363557
  have htrace : WordTrace (prefixWord ++ tailWord_3363557) baseStart_3363557 baseEnd_3363557 := by
    simpa [prefixWord, tailWord_3363557, baseEnd_3363557] using wordTrace_append hprefix tailTrace_3363557
  have hstable : (prefixWord ++ tailWord_3363557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363557).length < 2 ^ (prefixWord ++ tailWord_3363557).sum := by decide
  have hdescent : baseEnd_3363557 < baseStart_3363557 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363581 : List Nat := [1, 4, 1, 1, 1, 1, 6, 3, 1, 2, 2]
def baseStart_3363581 : Nat := 118140960795 + 3363581 * 2 ^ 59
def prefixEnd_3363581 : Nat := 4983230072969 + 3 ^ 40 * 3363581 * 2
def baseEnd_3363581 : Nat := 1727133773330709707568679

theorem tailTrace_3363581 : CollatzResearch.WordTrace tailWord_3363581 prefixEnd_3363581 1727133773330709707568679 := by
  unfold tailWord_3363581
  simp only [CollatzResearch.WordTrace]
  refine ⟨122679877627327965745298597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81786585084885310496865731 122679877627327965745298597)
  ·
    refine ⟨23002477055123993577243487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122679877627327965745298597 23002477055123993577243487)
    ·
      refine ⟨34503715582685990365865231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23002477055123993577243487 34503715582685990365865231)
      ·
        refine ⟨51755573374028985548797847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34503715582685990365865231 51755573374028985548797847)
        ·
          refine ⟨77633360061043478323196771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51755573374028985548797847 77633360061043478323196771)
          ·
            refine ⟨116450040091565217484795157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77633360061043478323196771 116450040091565217484795157)
            ·
              refine ⟨5458595629292119569599773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 116450040091565217484795157 5458595629292119569599773)
              ·
                refine ⟨2046973360984544838599915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5458595629292119569599773 2046973360984544838599915)
                ·
                  refine ⟨3070460041476817257899873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046973360984544838599915 3070460041476817257899873)
                  ·
                    refine ⟨2302845031107612943424905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3070460041476817257899873 2302845031107612943424905)
                    ·
                      refine ⟨1727133773330709707568679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2302845031107612943424905 1727133773330709707568679)
                      ·
                        rfl

theorem cell23_3363581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 6, 3, 1, 2, 2].length) (baseStart_3363581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363581 prefixEnd_3363581 := by exact prefixLift 3363581
  have htrace : WordTrace (prefixWord ++ tailWord_3363581) baseStart_3363581 baseEnd_3363581 := by
    simpa [prefixWord, tailWord_3363581, baseEnd_3363581] using wordTrace_append hprefix tailTrace_3363581
  have hstable : (prefixWord ++ tailWord_3363581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363581).length < 2 ^ (prefixWord ++ tailWord_3363581).sum := by decide
  have hdescent : baseEnd_3363581 < baseStart_3363581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363640 : List Nat := [2, 1, 2, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_3363640 : Nat := 118140960795 + 3363640 * 2 ^ 59
def prefixEnd_3363640 : Nat := 4983230072969 + 3 ^ 40 * 3363640 * 2
def baseEnd_3363640 : Nat := 1727164068689324976730907

theorem tailTrace_3363640 : CollatzResearch.WordTrace tailWord_3363640 prefixEnd_3363640 1727164068689324976730907 := by
  unfold tailWord_3363640
  simp only [CollatzResearch.WordTrace]
  refine ⟨61341014767057109410848187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81788019689409479214464249 61341014767057109410848187)
  ·
    refine ⟨92011522150585664116272281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61341014767057109410848187 92011522150585664116272281)
    ·
      refine ⟨69008641612939248087204211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92011522150585664116272281 69008641612939248087204211)
      ·
        refine ⟨103512962419408872130806317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69008641612939248087204211 103512962419408872130806317)
        ·
          refine ⟨38817360907278327049052369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103512962419408872130806317 38817360907278327049052369)
          ·
            refine ⟨29113020680458745286789277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38817360907278327049052369 29113020680458745286789277)
            ·
              refine ⟨10917382755172029482545979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29113020680458745286789277 10917382755172029482545979)
              ·
                refine ⟨16376074132758044223818969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10917382755172029482545979 16376074132758044223818969)
                ·
                  refine ⟨12282055599568533167864227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16376074132758044223818969 12282055599568533167864227)
                  ·
                    refine ⟨18423083399352799751796341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12282055599568533167864227 18423083399352799751796341)
                    ·
                      refine ⟨1727164068689324976730907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18423083399352799751796341 1727164068689324976730907)
                      ·
                        rfl

theorem cell23_3363640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_3363640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363640 prefixEnd_3363640 := by exact prefixLift 3363640
  have htrace : WordTrace (prefixWord ++ tailWord_3363640) baseStart_3363640 baseEnd_3363640 := by
    simpa [prefixWord, tailWord_3363640, baseEnd_3363640] using wordTrace_append hprefix tailTrace_3363640
  have hstable : (prefixWord ++ tailWord_3363640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363640).length < 2 ^ (prefixWord ++ tailWord_3363640).sum := by decide
  have hdescent : baseEnd_3363640 < baseStart_3363640 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363671 : List Nat := [1, 1, 3, 2, 4, 2, 1, 3, 2, 2, 2]
def baseStart_3363671 : Nat := 118140960795 + 3363671 * 2 ^ 59
def prefixEnd_3363671 : Nat := 4983230072969 + 3 ^ 40 * 3363671 * 2
def baseEnd_3363671 : Nat := 1727179986589614355443265

theorem tailTrace_3363671 : CollatzResearch.WordTrace tailWord_3363671 prefixEnd_3363671 1727179986589614355443265 := by
  unfold tailWord_3363671
  simp only [CollatzResearch.WordTrace]
  refine ⟨122683160197001911116074867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81788773464667940744049911 122683160197001911116074867)
  ·
    refine ⟨184024740295502866674112301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122683160197001911116074867 184024740295502866674112301)
    ·
      refine ⟨69009277610813575002792113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184024740295502866674112301 69009277610813575002792113)
      ·
        refine ⟨51756958208110181252094085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69009277610813575002792113 51756958208110181252094085)
        ·
          refine ⟨9704429664020658984767641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51756958208110181252094085 9704429664020658984767641)
          ·
            refine ⟨7278322248015494238575731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9704429664020658984767641 7278322248015494238575731)
            ·
              refine ⟨10917483372023241357863597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278322248015494238575731 10917483372023241357863597)
              ·
                refine ⟨4094056264508715509198849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10917483372023241357863597 4094056264508715509198849)
                ·
                  refine ⟨3070542198381536631899137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4094056264508715509198849 3070542198381536631899137)
                  ·
                    refine ⟨2302906648786152473924353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3070542198381536631899137 2302906648786152473924353)
                    ·
                      refine ⟨1727179986589614355443265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2302906648786152473924353 1727179986589614355443265)
                      ·
                        rfl

theorem cell23_3363671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 3, 2, 2, 2].length) (baseStart_3363671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363671 prefixEnd_3363671 := by exact prefixLift 3363671
  have htrace : WordTrace (prefixWord ++ tailWord_3363671) baseStart_3363671 baseEnd_3363671 := by
    simpa [prefixWord, tailWord_3363671, baseEnd_3363671] using wordTrace_append hprefix tailTrace_3363671
  have hstable : (prefixWord ++ tailWord_3363671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363671).length < 2 ^ (prefixWord ++ tailWord_3363671).sum := by decide
  have hdescent : baseEnd_3363671 < baseStart_3363671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363767 : List Nat := [1, 1, 3, 1, 3, 1, 5, 2, 6]
def baseStart_3363767 : Nat := 118140960795 + 3363767 * 2 ^ 59
def prefixEnd_3363767 : Nat := 4983230072969 + 3 ^ 40 * 3363767 * 2
def baseEnd_3363767 : Nat := 191914364525827331093647

theorem tailTrace_3363767 : CollatzResearch.WordTrace tailWord_3363767 prefixEnd_3363767 191914364525827331093647 := by
  unfold tailWord_3363767
  simp only [CollatzResearch.WordTrace]
  refine ⟨122686661604654119511569555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81791107736436079674379703 122686661604654119511569555)
  ·
    refine ⟨184029992406981179267354333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122686661604654119511569555 184029992406981179267354333)
    ·
      refine ⟨69011247152617942225257875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184029992406981179267354333 69011247152617942225257875)
      ·
        refine ⟨103516870728926913337886813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69011247152617942225257875 103516870728926913337886813)
        ·
          refine ⟨38818826523347592501707555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103516870728926913337886813 38818826523347592501707555)
          ·
            refine ⟨58228239785021388752561333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38818826523347592501707555 58228239785021388752561333)
            ·
              refine ⟨5458897479845755195552625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58228239785021388752561333 5458897479845755195552625)
              ·
                refine ⟨4094173109884316396664469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5458897479845755195552625 4094173109884316396664469)
                ·
                  refine ⟨191914364525827331093647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4094173109884316396664469 191914364525827331093647)
                  ·
                    rfl

theorem cell23_3363767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 5, 2, 6].length) (baseStart_3363767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363767 prefixEnd_3363767 := by exact prefixLift 3363767
  have htrace : WordTrace (prefixWord ++ tailWord_3363767) baseStart_3363767 baseEnd_3363767 := by
    simpa [prefixWord, tailWord_3363767, baseEnd_3363767] using wordTrace_append hprefix tailTrace_3363767
  have hstable : (prefixWord ++ tailWord_3363767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363767).length < 2 ^ (prefixWord ++ tailWord_3363767).sum := by decide
  have hdescent : baseEnd_3363767 < baseStart_3363767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363770 : List Nat := [3, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8]
def baseStart_3363770 : Nat := 118140960795 + 3363770 * 2 ^ 59
def prefixEnd_3363770 : Nat := 4983230072969 + 3 ^ 40 * 3363770 * 2
def baseEnd_3363770 : Nat := 1727230821174409468105309

theorem tailTrace_3363770 : CollatzResearch.WordTrace tailWord_3363770 prefixEnd_3363770 1727230821174409468105309 := by
  unfold tailWord_3363770
  simp only [CollatzResearch.WordTrace]
  refine ⟨30671692755910812755982191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81791180682428834015952509 30671692755910812755982191)
  ·
    refine ⟨46007539133866219133973287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30671692755910812755982191 46007539133866219133973287)
    ·
      refine ⟨69011308700799328700959931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46007539133866219133973287 69011308700799328700959931)
      ·
        refine ⟨103516963051198993051439897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69011308700799328700959931 103516963051198993051439897)
        ·
          refine ⟨77637722288399244788579923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103516963051198993051439897 77637722288399244788579923)
          ·
            refine ⟨116456583432598867182869885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77637722288399244788579923 116456583432598867182869885)
            ·
              refine ⟨43671218787224575193576207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116456583432598867182869885 43671218787224575193576207)
              ·
                refine ⟨65506828180836862790364311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43671218787224575193576207 65506828180836862790364311)
                ·
                  refine ⟨98260242271255294185546467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65506828180836862790364311 98260242271255294185546467)
                  ·
                    refine ⟨147390363406882941278319701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98260242271255294185546467 147390363406882941278319701)
                    ·
                      refine ⟨1727230821174409468105309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 147390363406882941278319701 1727230821174409468105309)
                      ·
                        rfl

theorem cell23_3363770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_3363770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363770 prefixEnd_3363770 := by exact prefixLift 3363770
  have htrace : WordTrace (prefixWord ++ tailWord_3363770) baseStart_3363770 baseEnd_3363770 := by
    simpa [prefixWord, tailWord_3363770, baseEnd_3363770] using wordTrace_append hprefix tailTrace_3363770
  have hstable : (prefixWord ++ tailWord_3363770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363770).length < 2 ^ (prefixWord ++ tailWord_3363770).sum := by decide
  have hdescent : baseEnd_3363770 < baseStart_3363770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363837 : List Nat := [1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 3]
def baseStart_3363837 : Nat := 118140960795 + 3363837 * 2 ^ 59
def prefixEnd_3363837 : Nat := 4983230072969 + 3 ^ 40 * 3363837 * 2
def baseEnd_3363837 : Nat := 1727265224378260705967501

theorem tailTrace_3363837 : CollatzResearch.WordTrace tailWord_3363837 prefixEnd_3363837 1727265224378260705967501 := by
  unfold tailWord_3363837
  simp only [CollatzResearch.WordTrace]
  refine ⟨122689214714400521466617765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81792809809600347644411843 122689214714400521466617765)
  ·
    refine ⟨23004227758950097774990831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122689214714400521466617765 23004227758950097774990831)
    ·
      refine ⟨34506341638425146662486247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23004227758950097774990831 34506341638425146662486247)
      ·
        refine ⟨51759512457637719993729371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34506341638425146662486247 51759512457637719993729371)
        ·
          refine ⟨77639268686456579990594057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51759512457637719993729371 77639268686456579990594057)
          ·
            refine ⟨58229451514842434992945543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77639268686456579990594057 58229451514842434992945543)
            ·
              refine ⟨87344177272263652489418315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58229451514842434992945543 87344177272263652489418315)
              ·
                refine ⟨131016265908395478734127473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87344177272263652489418315 131016265908395478734127473)
                ·
                  refine ⟨98262199431296609050595605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 131016265908395478734127473 98262199431296609050595605)
                  ·
                    refine ⟨4606040598342028549246669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98262199431296609050595605 4606040598342028549246669)
                    ·
                      refine ⟨1727265224378260705967501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4606040598342028549246669 1727265224378260705967501)
                      ·
                        rfl

theorem cell23_3363837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 1, 2, 6, 3].length) (baseStart_3363837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363837 prefixEnd_3363837 := by exact prefixLift 3363837
  have htrace : WordTrace (prefixWord ++ tailWord_3363837) baseStart_3363837 baseEnd_3363837 := by
    simpa [prefixWord, tailWord_3363837, baseEnd_3363837] using wordTrace_append hprefix tailTrace_3363837
  have hstable : (prefixWord ++ tailWord_3363837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363837).length < 2 ^ (prefixWord ++ tailWord_3363837).sum := by decide
  have hdescent : baseEnd_3363837 < baseStart_3363837 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363847 : List Nat := [1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 6]
def baseStart_3363847 : Nat := 118140960795 + 3363847 * 2 ^ 59
def prefixEnd_3363847 : Nat := 4983230072969 + 3 ^ 40 * 3363847 * 2
def baseEnd_3363847 : Nat := 1727270359184805666842455

theorem tailTrace_3363847 : CollatzResearch.WordTrace tailWord_3363847 prefixEnd_3363847 1727270359184805666842455 := by
  unfold tailWord_3363847
  simp only [CollatzResearch.WordTrace]
  refine ⟨122689579444364293174481795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81793052962909528782987863 122689579444364293174481795)
  ·
    refine ⟨184034369166546439761722693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122689579444364293174481795 184034369166546439761722693)
    ·
      refine ⟨34506444218727457455323005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184034369166546439761722693 34506444218727457455323005)
      ·
        refine ⟨12939916582022796545746127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34506444218727457455323005 12939916582022796545746127)
        ·
          refine ⟨19409874873034194818619191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12939916582022796545746127 19409874873034194818619191)
          ·
            refine ⟨29114812309551292227928787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19409874873034194818619191 29114812309551292227928787)
            ·
              refine ⟨43672218464326938341893181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29114812309551292227928787 43672218464326938341893181)
              ·
                refine ⟨16377081924122601878209943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43672218464326938341893181 16377081924122601878209943)
                ·
                  refine ⟨24565622886183902817314915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16377081924122601878209943 24565622886183902817314915)
                  ·
                    refine ⟨36848434329275854225972373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24565622886183902817314915 36848434329275854225972373)
                    ·
                      refine ⟨1727270359184805666842455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36848434329275854225972373 1727270359184805666842455)
                      ·
                        rfl

theorem cell23_3363847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_3363847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363847 prefixEnd_3363847 := by exact prefixLift 3363847
  have htrace : WordTrace (prefixWord ++ tailWord_3363847) baseStart_3363847 baseEnd_3363847 := by
    simpa [prefixWord, tailWord_3363847, baseEnd_3363847] using wordTrace_append hprefix tailTrace_3363847
  have hstable : (prefixWord ++ tailWord_3363847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363847).length < 2 ^ (prefixWord ++ tailWord_3363847).sum := by decide
  have hdescent : baseEnd_3363847 < baseStart_3363847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363851 : List Nat := [1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 4]
def baseStart_3363851 : Nat := 118140960795 + 3363851 * 2 ^ 59
def prefixEnd_3363851 : Nat := 4983230072969 + 3 ^ 40 * 3363851 * 2
def baseEnd_3363851 : Nat := 1727272413107423651192437

theorem tailTrace_3363851 : CollatzResearch.WordTrace tailWord_3363851 prefixEnd_3363851 1727272413107423651192437 := by
  unfold tailWord_3363851
  simp only [CollatzResearch.WordTrace]
  refine ⟨122689725336349801857627407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81793150224233201238418271 122689725336349801857627407)
  ·
    refine ⟨184034588004524702786441111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122689725336349801857627407 184034588004524702786441111)
    ·
      refine ⟨276051882006787054179661667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184034588004524702786441111 276051882006787054179661667)
      ·
        refine ⟨414077823010180581269492501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276051882006787054179661667 414077823010180581269492501)
        ·
          refine ⟨19409897953602214747007461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 414077823010180581269492501 19409897953602214747007461)
          ·
            refine ⟨3639355866300415265063899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19409897953602214747007461 3639355866300415265063899)
            ·
              refine ⟨5459033799450622897595849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639355866300415265063899 5459033799450622897595849)
              ·
                refine ⟨4094275349587967173196887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5459033799450622897595849 4094275349587967173196887)
                ·
                  refine ⟨6141413024381950759795331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094275349587967173196887 6141413024381950759795331)
                  ·
                    refine ⟨9212119536572926139692997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6141413024381950759795331 9212119536572926139692997)
                    ·
                      refine ⟨1727272413107423651192437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9212119536572926139692997 1727272413107423651192437)
                      ·
                        rfl

theorem cell23_3363851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 1, 4].length) (baseStart_3363851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363851 prefixEnd_3363851 := by exact prefixLift 3363851
  have htrace : WordTrace (prefixWord ++ tailWord_3363851) baseStart_3363851 baseEnd_3363851 := by
    simpa [prefixWord, tailWord_3363851, baseEnd_3363851] using wordTrace_append hprefix tailTrace_3363851
  have hstable : (prefixWord ++ tailWord_3363851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363851).length < 2 ^ (prefixWord ++ tailWord_3363851).sum := by decide
  have hdescent : baseEnd_3363851 < baseStart_3363851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363864 : List Nat := [2, 1, 2, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_3363864 : Nat := 118140960795 + 3363864 * 2 ^ 59
def prefixEnd_3363864 : Nat := 4983230072969 + 3 ^ 40 * 3363864 * 2
def baseEnd_3363864 : Nat := 1727279088355932100329877

theorem tailTrace_3363864 : CollatzResearch.WordTrace tailWord_3363864 prefixEnd_3363864 1727279088355932100329877 := by
  unfold tailWord_3363864
  simp only [CollatzResearch.WordTrace]
  refine ⟨61345099742651352538925323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81793466323535136718567097 61345099742651352538925323)
  ·
    refine ⟨92017649613977028808387985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61345099742651352538925323 92017649613977028808387985)
    ·
      refine ⟨69013237210482771606290989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92017649613977028808387985 69013237210482771606290989)
      ·
        refine ⟨25879963953931039352359121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69013237210482771606290989 25879963953931039352359121)
        ·
          refine ⟨19409972965448279514269341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25879963953931039352359121 19409972965448279514269341)
          ·
            refine ⟨7278739862043104817851003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19409972965448279514269341 7278739862043104817851003)
            ·
              refine ⟨10918109793064657226776505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7278739862043104817851003 10918109793064657226776505)
              ·
                refine ⟨8188582344798492920082379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10918109793064657226776505 8188582344798492920082379)
                ·
                  refine ⟨12282873517197739380123569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8188582344798492920082379 12282873517197739380123569)
                  ·
                    refine ⟨9212155137898304535092677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12282873517197739380123569 9212155137898304535092677)
                    ·
                      refine ⟨1727279088355932100329877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9212155137898304535092677 1727279088355932100329877)
                      ·
                        rfl

theorem cell23_3363864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_3363864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363864 prefixEnd_3363864 := by exact prefixLift 3363864
  have htrace : WordTrace (prefixWord ++ tailWord_3363864) baseStart_3363864 baseEnd_3363864 := by
    simpa [prefixWord, tailWord_3363864, baseEnd_3363864] using wordTrace_append hprefix tailTrace_3363864
  have hstable : (prefixWord ++ tailWord_3363864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363864).length < 2 ^ (prefixWord ++ tailWord_3363864).sum := by decide
  have hdescent : baseEnd_3363864 < baseStart_3363864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363868 : List Nat := [2, 2, 3, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_3363868 : Nat := 118140960795 + 3363868 * 2 ^ 59
def prefixEnd_3363868 : Nat := 4983230072969 + 3 ^ 40 * 3363868 * 2
def baseEnd_3363868 : Nat := 1727281142278550084679859

theorem tailTrace_3363868 : CollatzResearch.WordTrace tailWord_3363868 prefixEnd_3363868 1727281142278550084679859 := by
  unfold tailWord_3363868
  simp only [CollatzResearch.WordTrace]
  refine ⟨61345172688644106880498129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81793563584858809173997505 61345172688644106880498129)
  ·
    refine ⟨46008879516483080160373597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61345172688644106880498129 46008879516483080160373597)
    ·
      refine ⟨17253329818681155060140099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46008879516483080160373597 17253329818681155060140099)
      ·
        refine ⟨25879994728021732590210149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17253329818681155060140099 25879994728021732590210149)
        ·
          refine ⟨4852499011504074860664403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25879994728021732590210149 4852499011504074860664403)
          ·
            refine ⟨7278748517256112290996605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852499011504074860664403 7278748517256112290996605)
            ·
              refine ⟨2729530693971042109123727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7278748517256112290996605 2729530693971042109123727)
              ·
                refine ⟨4094296040956563163685591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729530693971042109123727 4094296040956563163685591)
                ·
                  refine ⟨6141444061434844745528387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094296040956563163685591 6141444061434844745528387)
                  ·
                    refine ⟨9212166092152267118292581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6141444061434844745528387 9212166092152267118292581)
                    ·
                      refine ⟨1727281142278550084679859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9212166092152267118292581 1727281142278550084679859)
                      ·
                        rfl

theorem cell23_3363868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_3363868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363868 prefixEnd_3363868 := by exact prefixLift 3363868
  have htrace : WordTrace (prefixWord ++ tailWord_3363868) baseStart_3363868 baseEnd_3363868 := by
    simpa [prefixWord, tailWord_3363868, baseEnd_3363868] using wordTrace_append hprefix tailTrace_3363868
  have hstable : (prefixWord ++ tailWord_3363868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363868).length < 2 ^ (prefixWord ++ tailWord_3363868).sum := by decide
  have hdescent : baseEnd_3363868 < baseStart_3363868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363901 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 3]
def baseStart_3363901 : Nat := 118140960795 + 3363901 * 2 ^ 59
def prefixEnd_3363901 : Nat := 4983230072969 + 3 ^ 40 * 3363901 * 2
def baseEnd_3363901 : Nat := 1727298087140148455567207

theorem tailTrace_3363901 : CollatzResearch.WordTrace tailWord_3363901 prefixEnd_3363901 1727298087140148455567207 := by
  unfold tailWord_3363901
  simp only [CollatzResearch.WordTrace]
  refine ⟨122691548986168660396947557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81794365990779106931298371 122691548986168660396947557)
  ·
    refine ⟨23004665434906623824427667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122691548986168660396947557 23004665434906623824427667)
    ·
      refine ⟨34506998152359935736641501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23004665434906623824427667 34506998152359935736641501)
      ·
        refine ⟨12940124307134975901240563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34506998152359935736641501 12940124307134975901240563)
        ·
          refine ⟨19410186460702463851860845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940124307134975901240563 19410186460702463851860845)
          ·
            refine ⟨7278819922763423944447817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19410186460702463851860845 7278819922763423944447817)
            ·
              refine ⟨5459114942072567958335863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7278819922763423944447817 5459114942072567958335863)
              ·
                refine ⟨8188672413108851937503795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459114942072567958335863 8188672413108851937503795)
                ·
                  refine ⟨12283008619663277906255693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8188672413108851937503795 12283008619663277906255693)
                  ·
                    refine ⟨4606128232373729214845885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12283008619663277906255693 4606128232373729214845885)
                    ·
                      refine ⟨1727298087140148455567207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4606128232373729214845885 1727298087140148455567207)
                      ·
                        rfl

theorem cell23_3363901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_3363901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363901 prefixEnd_3363901 := by exact prefixLift 3363901
  have htrace : WordTrace (prefixWord ++ tailWord_3363901) baseStart_3363901 baseEnd_3363901 := by
    simpa [prefixWord, tailWord_3363901, baseEnd_3363901] using wordTrace_append hprefix tailTrace_3363901
  have hstable : (prefixWord ++ tailWord_3363901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363901).length < 2 ^ (prefixWord ++ tailWord_3363901).sum := by decide
  have hdescent : baseEnd_3363901 < baseStart_3363901 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363907 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 4]
def baseStart_3363907 : Nat := 118140960795 + 3363907 * 2 ^ 59
def prefixEnd_3363907 : Nat := 4983230072969 + 3 ^ 40 * 3363907 * 2
def baseEnd_3363907 : Nat := 1727301168024075432092179

theorem tailTrace_3363907 : CollatzResearch.WordTrace tailWord_3363907 prefixEnd_3363907 1727301168024075432092179 := by
  unfold tailWord_3363907
  simp only [CollatzResearch.WordTrace]
  refine ⟨122691767824146923421665975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81794511882764615614443983 122691767824146923421665975)
  ·
    refine ⟨184037651736220385132498963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122691767824146923421665975 184037651736220385132498963)
    ·
      refine ⟨276056477604330577698748445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184037651736220385132498963 276056477604330577698748445)
      ·
        refine ⟨103521179101623966637030667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 276056477604330577698748445 103521179101623966637030667)
        ·
          refine ⟨155281768652435949955546001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103521179101623966637030667 155281768652435949955546001)
          ·
            refine ⟨116461326489326962466659501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155281768652435949955546001 116461326489326962466659501)
            ·
              refine ⟨43672997433497610924997313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116461326489326962466659501 43672997433497610924997313)
              ·
                refine ⟨32754748075123208193747985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43672997433497610924997313 32754748075123208193747985)
                ·
                  refine ⟨24566061056342406145310989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32754748075123208193747985 24566061056342406145310989)
                  ·
                    refine ⟨9212272896128402304491621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24566061056342406145310989 9212272896128402304491621)
                    ·
                      refine ⟨1727301168024075432092179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9212272896128402304491621 1727301168024075432092179)
                      ·
                        rfl

theorem cell23_3363907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_3363907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363907 prefixEnd_3363907 := by exact prefixLift 3363907
  have htrace : WordTrace (prefixWord ++ tailWord_3363907) baseStart_3363907 baseEnd_3363907 := by
    simpa [prefixWord, tailWord_3363907, baseEnd_3363907] using wordTrace_append hprefix tailTrace_3363907
  have hstable : (prefixWord ++ tailWord_3363907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363907).length < 2 ^ (prefixWord ++ tailWord_3363907).sum := by decide
  have hdescent : baseEnd_3363907 < baseStart_3363907 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363911 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 3, 3, 2]
def baseStart_3363911 : Nat := 118140960795 + 3363911 * 2 ^ 59
def prefixEnd_3363911 : Nat := 4983230072969 + 3 ^ 40 * 3363911 * 2
def baseEnd_3363911 : Nat := 1727303221946693416442161

theorem tailTrace_3363911 : CollatzResearch.WordTrace tailWord_3363911 prefixEnd_3363911 1727303221946693416442161 := by
  unfold tailWord_3363911
  simp only [CollatzResearch.WordTrace]
  refine ⟨122691913716132432104811587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81794609144088288069874391 122691913716132432104811587)
  ·
    refine ⟨184037870574198648157217381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122691913716132432104811587 184037870574198648157217381)
    ·
      refine ⟨34507100732662246529478259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 184037870574198648157217381 34507100732662246529478259)
      ·
        refine ⟨51760651098993369794217389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34507100732662246529478259 51760651098993369794217389)
        ·
          refine ⟨19410244162122513672831521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51760651098993369794217389 19410244162122513672831521)
          ·
            refine ⟨14557683121591885254623641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19410244162122513672831521 14557683121591885254623641)
            ·
              refine ⟨10918262341193913940967731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14557683121591885254623641 10918262341193913940967731)
              ·
                refine ⟨16377393511790870911451597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10918262341193913940967731 16377393511790870911451597)
                ·
                  refine ⟨6141522566921576591794349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16377393511790870911451597 6141522566921576591794349)
                  ·
                    refine ⟨2303070962595591221922881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6141522566921576591794349 2303070962595591221922881)
                    ·
                      refine ⟨1727303221946693416442161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303070962595591221922881 1727303221946693416442161)
                      ·
                        rfl

theorem cell23_3363911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_3363911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363911 prefixEnd_3363911 := by exact prefixLift 3363911
  have htrace : WordTrace (prefixWord ++ tailWord_3363911) baseStart_3363911 baseEnd_3363911 := by
    simpa [prefixWord, tailWord_3363911, baseEnd_3363911] using wordTrace_append hprefix tailTrace_3363911
  have hstable : (prefixWord ++ tailWord_3363911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363911).length < 2 ^ (prefixWord ++ tailWord_3363911).sum := by decide
  have hdescent : baseEnd_3363911 < baseStart_3363911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363927 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 5]
def baseStart_3363927 : Nat := 118140960795 + 3363927 * 2 ^ 59
def prefixEnd_3363927 : Nat := 4983230072969 + 3 ^ 40 * 3363927 * 2
def baseEnd_3363927 : Nat := 1727311437637165353842087

theorem tailTrace_3363927 : CollatzResearch.WordTrace tailWord_3363927 prefixEnd_3363927 1727311437637165353842087 := by
  unfold tailWord_3363927
  simp only [CollatzResearch.WordTrace]
  refine ⟨122692497284074466837394035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81794998189382977891596023 122692497284074466837394035)
  ·
    refine ⟨184038745926111700256091053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122692497284074466837394035 184038745926111700256091053)
    ·
      refine ⟨69014529722291887596034145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 184038745926111700256091053 69014529722291887596034145)
      ·
        refine ⟨51760897291718915697025609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69014529722291887596034145 51760897291718915697025609)
        ·
          refine ⟨38820672968789186772769207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51760897291718915697025609 38820672968789186772769207)
          ·
            refine ⟨58231009453183780159153811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38820672968789186772769207 58231009453183780159153811)
            ·
              refine ⟨87346514179775670238730717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58231009453183780159153811 87346514179775670238730717)
              ·
                refine ⟨32754942817415876339524019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87346514179775670238730717 32754942817415876339524019)
                ·
                  refine ⟨49132414226123814509286029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32754942817415876339524019 49132414226123814509286029)
                  ·
                    refine ⟨18424655334796430440982261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49132414226123814509286029 18424655334796430440982261)
                    ·
                      refine ⟨1727311437637165353842087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18424655334796430440982261 1727311437637165353842087)
                      ·
                        rfl

theorem cell23_3363927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_3363927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363927 prefixEnd_3363927 := by exact prefixLift 3363927
  have htrace : WordTrace (prefixWord ++ tailWord_3363927) baseStart_3363927 baseEnd_3363927 := by
    simpa [prefixWord, tailWord_3363927, baseEnd_3363927] using wordTrace_append hprefix tailTrace_3363927
  have hstable : (prefixWord ++ tailWord_3363927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363927).length < 2 ^ (prefixWord ++ tailWord_3363927).sum := by decide
  have hdescent : baseEnd_3363927 < baseStart_3363927 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363954 : List Nat := [3, 2, 1, 2, 2, 1, 1, 3, 2, 2, 4]
def baseStart_3363954 : Nat := 118140960795 + 3363954 * 2 ^ 59
def prefixEnd_3363954 : Nat := 4983230072969 + 3 ^ 40 * 3363954 * 2
def baseEnd_3363954 : Nat := 1727325301614836748204463

theorem tailTrace_3363954 : CollatzResearch.WordTrace tailWord_3363954 prefixEnd_3363954 1727325301614836748204463 := by
  unfold tailWord_3363954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30673370513744162612156729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81795654703317766965751277 30673370513744162612156729)
  ·
    refine ⟨23005027885308121959117547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30673370513744162612156729 23005027885308121959117547)
    ·
      refine ⟨34507541827962182938676321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23005027885308121959117547 34507541827962182938676321)
      ·
        refine ⟨25880656370971637204007241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34507541827962182938676321 25880656370971637204007241)
        ·
          refine ⟨19410492278228727903005431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25880656370971637204007241 19410492278228727903005431)
          ·
            refine ⟨29115738417343091854508147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19410492278228727903005431 29115738417343091854508147)
            ·
              refine ⟨43673607626014637781762221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29115738417343091854508147 43673607626014637781762221)
              ·
                refine ⟨16377602859755489168160833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43673607626014637781762221 16377602859755489168160833)
                ·
                  refine ⟨12283202144816616876120625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16377602859755489168160833 12283202144816616876120625)
                  ·
                    refine ⟨9212401608612462657090469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12283202144816616876120625 9212401608612462657090469)
                    ·
                      refine ⟨1727325301614836748204463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9212401608612462657090469 1727325301614836748204463)
                      ·
                        rfl

theorem cell23_3363954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 3, 2, 2, 4].length) (baseStart_3363954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363954 prefixEnd_3363954 := by exact prefixLift 3363954
  have htrace : WordTrace (prefixWord ++ tailWord_3363954) baseStart_3363954 baseEnd_3363954 := by
    simpa [prefixWord, tailWord_3363954, baseEnd_3363954] using wordTrace_append hprefix tailTrace_3363954
  have hstable : (prefixWord ++ tailWord_3363954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363954).length < 2 ^ (prefixWord ++ tailWord_3363954).sum := by decide
  have hdescent : baseEnd_3363954 < baseStart_3363954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3363998 : List Nat := [4, 3, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3363998 : Nat := 118140960795 + 3363998 * 2 ^ 59
def prefixEnd_3363998 : Nat := 4983230072969 + 3 ^ 40 * 3363998 * 2
def baseEnd_3363998 : Nat := 191927543862626064006029

theorem tailTrace_3363998 : CollatzResearch.WordTrace tailWord_3363998 prefixEnd_3363998 191927543862626064006029 := by
  unfold tailWord_3363998
  simp only [CollatzResearch.WordTrace]
  refine ⟨15336885858352155745403581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81796724577878163975485765 15336885858352155745403581)
  ·
    refine ⟨5751332196882058404526343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15336885858352155745403581 5751332196882058404526343)
    ·
      refine ⟨8626998295323087606789515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5751332196882058404526343 8626998295323087606789515)
      ·
        refine ⟨12940497442984631410184273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8626998295323087606789515 12940497442984631410184273)
        ·
          refine ⟨9705373082238473557638205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12940497442984631410184273 9705373082238473557638205)
          ·
            refine ⟨3639514905839427584114327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9705373082238473557638205 3639514905839427584114327)
            ·
              refine ⟨5459272358759141376171491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639514905839427584114327 5459272358759141376171491)
              ·
                refine ⟨8188908538138712064257237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459272358759141376171491 8188908538138712064257237)
                ·
                  refine ⟨191927543862626064006029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8188908538138712064257237 191927543862626064006029)
                  ·
                    rfl

theorem cell23_3363998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3363998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3363998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3363998 prefixEnd_3363998 := by exact prefixLift 3363998
  have htrace : WordTrace (prefixWord ++ tailWord_3363998) baseStart_3363998 baseEnd_3363998 := by
    simpa [prefixWord, tailWord_3363998, baseEnd_3363998] using wordTrace_append hprefix tailTrace_3363998
  have hstable : (prefixWord ++ tailWord_3363998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3363998).length < 2 ^ (prefixWord ++ tailWord_3363998).sum := by decide
  have hdescent : baseEnd_3363998 < baseStart_3363998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3363998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364001 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 2, 5, 2]
def baseStart_3364001 : Nat := 118140960795 + 3364001 * 2 ^ 59
def prefixEnd_3364001 : Nat := 4983230072969 + 3 ^ 40 * 3364001 * 2
def baseEnd_3364001 : Nat := 1727349435205598064316747

theorem tailTrace_3364001 : CollatzResearch.WordTrace tailWord_3364001 prefixEnd_3364001 1727349435205598064316747 := by
  unfold tailWord_3364001
  simp only [CollatzResearch.WordTrace]
  refine ⟨122695196285806377475587857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81796797523870918317058571 122695196285806377475587857)
  ·
    refine ⟨92021397214354783106690893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122695196285806377475587857 92021397214354783106690893)
    ·
      refine ⟨34508023955383043665009085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92021397214354783106690893 34508023955383043665009085)
      ·
        refine ⟨12940508983268641374378407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34508023955383043665009085 12940508983268641374378407)
        ·
          refine ⟨19410763474902962061567611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12940508983268641374378407 19410763474902962061567611)
          ·
            refine ⟨29116145212354443092351417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19410763474902962061567611 29116145212354443092351417)
            ·
              refine ⟨21837108909265832319263563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29116145212354443092351417 21837108909265832319263563)
              ·
                refine ⟨32755663363898748478895345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21837108909265832319263563 32755663363898748478895345)
                ·
                  refine ⟨24566747522924061359171509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32755663363898748478895345 24566747522924061359171509)
                  ·
                    refine ⟨2303132580274130752422329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24566747522924061359171509 2303132580274130752422329)
                    ·
                      refine ⟨1727349435205598064316747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303132580274130752422329 1727349435205598064316747)
                      ·
                        rfl

theorem cell23_3364001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 5, 2].length) (baseStart_3364001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364001 prefixEnd_3364001 := by exact prefixLift 3364001
  have htrace : WordTrace (prefixWord ++ tailWord_3364001) baseStart_3364001 baseEnd_3364001 := by
    simpa [prefixWord, tailWord_3364001, baseEnd_3364001] using wordTrace_append hprefix tailTrace_3364001
  have hstable : (prefixWord ++ tailWord_3364001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364001).length < 2 ^ (prefixWord ++ tailWord_3364001).sum := by decide
  have hdescent : baseEnd_3364001 < baseStart_3364001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364004 : List Nat := [2, 3, 1, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_3364004 : Nat := 118140960795 + 3364004 * 2 ^ 59
def prefixEnd_3364004 : Nat := 4983230072969 + 3 ^ 40 * 3364004 * 2
def baseEnd_3364004 : Nat := 1727350975647561552579233

theorem tailTrace_3364004 : CollatzResearch.WordTrace tailWord_3364004 prefixEnd_3364004 1727350975647561552579233 := by
  unfold tailWord_3364004
  simp only [CollatzResearch.WordTrace]
  refine ⟨61347652852397754493973533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81796870469863672658631377 61347652852397754493973533)
  ·
    refine ⟨23005369819649157935240075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61347652852397754493973533 23005369819649157935240075)
    ·
      refine ⟨34508054729473736902860113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23005369819649157935240075 34508054729473736902860113)
      ·
        refine ⟨25881041047105302677145085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34508054729473736902860113 25881041047105302677145085)
        ·
          refine ⟨9705390392664488503929407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25881041047105302677145085 9705390392664488503929407)
          ·
            refine ⟨14558085588996732755894111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9705390392664488503929407 14558085588996732755894111)
            ·
              refine ⟨21837128383495099133841167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14558085588996732755894111 21837128383495099133841167)
              ·
                refine ⟨32755692575242648700761751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21837128383495099133841167 32755692575242648700761751)
                ·
                  refine ⟨49133538862863973051142627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32755692575242648700761751 49133538862863973051142627)
                  ·
                    refine ⟨73700308294295959576713941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49133538862863973051142627 73700308294295959576713941)
                    ·
                      refine ⟨1727350975647561552579233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73700308294295959576713941 1727350975647561552579233)
                      ·
                        rfl

theorem cell23_3364004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_3364004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364004 prefixEnd_3364004 := by exact prefixLift 3364004
  have htrace : WordTrace (prefixWord ++ tailWord_3364004) baseStart_3364004 baseEnd_3364004 := by
    simpa [prefixWord, tailWord_3364004, baseEnd_3364004] using wordTrace_append hprefix tailTrace_3364004
  have hstable : (prefixWord ++ tailWord_3364004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364004).length < 2 ^ (prefixWord ++ tailWord_3364004).sum := by decide
  have hdescent : baseEnd_3364004 < baseStart_3364004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364101 : List Nat := [1, 3, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_3364101 : Nat := 118140960795 + 3364101 * 2 ^ 59
def prefixEnd_3364101 : Nat := 4983230072969 + 3 ^ 40 * 3364101 * 2
def baseEnd_3364101 : Nat := 575800261090349224355429

theorem tailTrace_3364101 : CollatzResearch.WordTrace tailWord_3364101 prefixEnd_3364101 575800261090349224355429 := by
  unfold tailWord_3364101
  simp only [CollatzResearch.WordTrace]
  refine ⟨122698843585444094554228157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81799229056962729702818771 122698843585444094554228157)
  ·
    refine ⟨46012066344541535457835559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122698843585444094554228157 46012066344541535457835559)
    ·
      refine ⟨69018099516812303186753339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46012066344541535457835559 69018099516812303186753339)
      ·
        refine ⟨103527149275218454780130009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69018099516812303186753339 103527149275218454780130009)
        ·
          refine ⟨77645361956413841085097507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103527149275218454780130009 77645361956413841085097507)
          ·
            refine ⟨116468042934620761627646261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77645361956413841085097507 116468042934620761627646261)
            ·
              refine ⟨10918879025120696402591837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116468042934620761627646261 10918879025120696402591837)
              ·
                refine ⟨4094579634420261150971939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10918879025120696402591837 4094579634420261150971939)
                ·
                  refine ⟨6141869451630391726457909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4094579634420261150971939 6141869451630391726457909)
                  ·
                    refine ⟨575800261090349224355429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6141869451630391726457909 575800261090349224355429)
                    ·
                      rfl

theorem cell23_3364101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_3364101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364101 prefixEnd_3364101 := by exact prefixLift 3364101
  have htrace : WordTrace (prefixWord ++ tailWord_3364101) baseStart_3364101 baseEnd_3364101 := by
    simpa [prefixWord, tailWord_3364101, baseEnd_3364101] using wordTrace_append hprefix tailTrace_3364101
  have hstable : (prefixWord ++ tailWord_3364101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364101).length < 2 ^ (prefixWord ++ tailWord_3364101).sum := by decide
  have hdescent : baseEnd_3364101 < baseStart_3364101 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364131 : List Nat := [1, 1, 1, 4, 2, 3, 3, 1, 1, 6]
def baseStart_3364131 : Nat := 118140960795 + 3364131 * 2 ^ 59
def prefixEnd_3364131 : Nat := 4983230072969 + 3 ^ 40 * 3364131 * 2
def baseEnd_3364131 : Nat := 575805395896894185230383

theorem tailTrace_3364131 : CollatzResearch.WordTrace tailWord_3364131 prefixEnd_3364131 575805395896894185230383 := by
  unfold tailWord_3364131
  simp only [CollatzResearch.WordTrace]
  refine ⟨122699937775335409677820247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81799958516890273118546831 122699937775335409677820247)
  ·
    refine ⟨184049906663003114516730371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122699937775335409677820247 184049906663003114516730371)
    ·
      refine ⟨276074859994504671775095557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184049906663003114516730371 276074859994504671775095557)
      ·
        refine ⟨51764036248969625957830417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 276074859994504671775095557 51764036248969625957830417)
        ·
          refine ⟨38823027186727219468372813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51764036248969625957830417 38823027186727219468372813)
          ·
            refine ⟨14558635195022707300639805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38823027186727219468372813 14558635195022707300639805)
            ·
              refine ⟨5459488198133515237739927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14558635195022707300639805 5459488198133515237739927)
              ·
                refine ⟨8189232297200272856609891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459488198133515237739927 8189232297200272856609891)
                ·
                  refine ⟨12283848445800409284914837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8189232297200272856609891 12283848445800409284914837)
                  ·
                    refine ⟨575805395896894185230383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12283848445800409284914837 575805395896894185230383)
                    ·
                      rfl

theorem cell23_3364131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 6].length) (baseStart_3364131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364131 prefixEnd_3364131 := by exact prefixLift 3364131
  have htrace : WordTrace (prefixWord ++ tailWord_3364131) baseStart_3364131 baseEnd_3364131 := by
    simpa [prefixWord, tailWord_3364131, baseEnd_3364131] using wordTrace_append hprefix tailTrace_3364131
  have hstable : (prefixWord ++ tailWord_3364131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364131).length < 2 ^ (prefixWord ++ tailWord_3364131).sum := by decide
  have hdescent : baseEnd_3364131 < baseStart_3364131 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364144 : List Nat := [2, 1, 1, 1, 2, 2, 5, 9]
def baseStart_3364144 : Nat := 118140960795 + 3364144 * 2 ^ 59
def prefixEnd_3364144 : Nat := 4983230072969 + 3 ^ 40 * 3364144 * 2
def baseEnd_3364144 : Nat := 63978624553303370549207

theorem tailTrace_3364144 : CollatzResearch.WordTrace tailWord_3364144 prefixEnd_3364144 63978624553303370549207 := by
  unfold tailWord_3364144
  simp only [CollatzResearch.WordTrace]
  refine ⟨61350205962144156449021743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81800274616192208598695657 61350205962144156449021743)
  ·
    refine ⟨92025308943216234673532615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61350205962144156449021743 92025308943216234673532615)
    ·
      refine ⟨138037963414824352010298923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92025308943216234673532615 138037963414824352010298923)
      ·
        refine ⟨207056945122236528015448385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138037963414824352010298923 207056945122236528015448385)
        ·
          refine ⟨155292708841677396011586289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207056945122236528015448385 155292708841677396011586289)
          ·
            refine ⟨116469531631258047008689717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155292708841677396011586289 116469531631258047008689717)
            ·
              refine ⟨10919018590430441907064661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116469531631258047008689717 10919018590430441907064661)
              ·
                refine ⟨63978624553303370549207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10919018590430441907064661 63978624553303370549207)
                ·
                  rfl

theorem cell23_3364144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 5, 9].length) (baseStart_3364144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364144 prefixEnd_3364144 := by exact prefixLift 3364144
  have htrace : WordTrace (prefixWord ++ tailWord_3364144) baseStart_3364144 baseEnd_3364144 := by
    simpa [prefixWord, tailWord_3364144, baseEnd_3364144] using wordTrace_append hprefix tailTrace_3364144
  have hstable : (prefixWord ++ tailWord_3364144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364144).length < 2 ^ (prefixWord ++ tailWord_3364144).sum := by decide
  have hdescent : baseEnd_3364144 < baseStart_3364144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364148 : List Nat := [2, 5, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_3364148 : Nat := 118140960795 + 3364148 * 2 ^ 59
def prefixEnd_3364148 : Nat := 4983230072969 + 3 ^ 40 * 3364148 * 2
def baseEnd_3364148 : Nat := 575808305620602996392857

theorem tailTrace_3364148 : CollatzResearch.WordTrace tailWord_3364148 prefixEnd_3364148 575808305620602996392857 := by
  unfold tailWord_3364148
  simp only [CollatzResearch.WordTrace]
  refine ⟨61350278908136910790594549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81800371877515881054126065 61350278908136910790594549)
  ·
    refine ⟨5751588647637835386618239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61350278908136910790594549 5751588647637835386618239)
    ·
      refine ⟨8627382971456753079927359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5751588647637835386618239 8627382971456753079927359)
      ·
        refine ⟨12941074457185129619891039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8627382971456753079927359 12941074457185129619891039)
        ·
          refine ⟨19411611685777694429836559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12941074457185129619891039 19411611685777694429836559)
          ·
            refine ⟨29117417528666541644754839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19411611685777694429836559 29117417528666541644754839)
            ·
              refine ⟨43676126292999812467132259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29117417528666541644754839 43676126292999812467132259)
              ·
                refine ⟨65514189439499718700698389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43676126292999812467132259 65514189439499718700698389)
                ·
                  refine ⟨3070977629976549314095237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65514189439499718700698389 3070977629976549314095237)
                  ·
                    refine ⟨575808305620602996392857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3070977629976549314095237 575808305620602996392857)
                    ·
                      rfl

theorem cell23_3364148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_3364148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364148 prefixEnd_3364148 := by exact prefixLift 3364148
  have htrace : WordTrace (prefixWord ++ tailWord_3364148) baseStart_3364148 baseEnd_3364148 := by
    simpa [prefixWord, tailWord_3364148, baseEnd_3364148] using wordTrace_append hprefix tailTrace_3364148
  have hstable : (prefixWord ++ tailWord_3364148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364148).length < 2 ^ (prefixWord ++ tailWord_3364148).sum := by decide
  have hdescent : baseEnd_3364148 < baseStart_3364148 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364158 : List Nat := [4, 2, 1, 2, 1, 1, 4, 1, 1, 1, 5]
def baseStart_3364158 : Nat := 118140960795 + 3364158 * 2 ^ 59
def prefixEnd_3364158 : Nat := 4983230072969 + 3 ^ 40 * 3364158 * 2
def baseEnd_3364158 : Nat := 1727430051668353950053525

theorem tailTrace_3364158 : CollatzResearch.WordTrace tailWord_3364158 prefixEnd_3364158 1727430051668353950053525 := by
  unfold tailWord_3364158
  simp only [CollatzResearch.WordTrace]
  refine ⟨15337615318279699161131641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81800615030825062192702085 15337615318279699161131641)
  ·
    refine ⟨11503211488709774370848731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15337615318279699161131641 11503211488709774370848731)
    ·
      refine ⟨17254817233064661556273097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11503211488709774370848731 17254817233064661556273097)
      ·
        refine ⟨12941112924798496167204823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17254817233064661556273097 12941112924798496167204823)
        ·
          refine ⟨19411669387197744250807235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12941112924798496167204823 19411669387197744250807235)
          ·
            refine ⟨29117504080796616376210853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19411669387197744250807235 29117504080796616376210853)
            ·
              refine ⟨5459532015149365570539535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29117504080796616376210853 5459532015149365570539535)
              ·
                refine ⟨8189298022724048355809303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459532015149365570539535 8189298022724048355809303)
                ·
                  refine ⟨12283947034086072533713955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8189298022724048355809303 12283947034086072533713955)
                  ·
                    refine ⟨18425920551129108800570933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12283947034086072533713955 18425920551129108800570933)
                    ·
                      refine ⟨1727430051668353950053525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18425920551129108800570933 1727430051668353950053525)
                      ·
                        rfl

theorem cell23_3364158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_3364158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364158 prefixEnd_3364158 := by exact prefixLift 3364158
  have htrace : WordTrace (prefixWord ++ tailWord_3364158) baseStart_3364158 baseEnd_3364158 := by
    simpa [prefixWord, tailWord_3364158, baseEnd_3364158] using wordTrace_append hprefix tailTrace_3364158
  have hstable : (prefixWord ++ tailWord_3364158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364158).length < 2 ^ (prefixWord ++ tailWord_3364158).sum := by decide
  have hdescent : baseEnd_3364158 < baseStart_3364158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364161 : List Nat := [1, 2, 5, 2, 1, 1, 11]
def baseStart_3364161 : Nat := 118140960795 + 3364161 * 2 ^ 59
def prefixEnd_3364161 : Nat := 4983230072969 + 3 ^ 40 * 3364161 * 2
def baseEnd_3364161 : Nat := 21326315951979227633531

theorem tailTrace_3364161 : CollatzResearch.WordTrace tailWord_3364161 prefixEnd_3364161 21326315951979227633531 := by
  unfold tailWord_3364161
  simp only [CollatzResearch.WordTrace]
  refine ⟨122701031965226724801412337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81800687976817816534274891 122701031965226724801412337)
  ·
    refine ⟨92025773973920043601059253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122701031965226724801412337 92025773973920043601059253)
    ·
      refine ⟨8627416310055004087599305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92025773973920043601059253 8627416310055004087599305)
      ·
        refine ⟨6470562232541253065699479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8627416310055004087599305 6470562232541253065699479)
        ·
          refine ⟨9705843348811879598549219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6470562232541253065699479 9705843348811879598549219)
          ·
            refine ⟨14558765023217819397823829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9705843348811879598549219 14558765023217819397823829)
            ·
              refine ⟨21326315951979227633531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14558765023217819397823829 21326315951979227633531)
              ·
                rfl

theorem cell23_3364161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 11].length) (baseStart_3364161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364161 prefixEnd_3364161 := by exact prefixLift 3364161
  have htrace : WordTrace (prefixWord ++ tailWord_3364161) baseStart_3364161 baseEnd_3364161 := by
    simpa [prefixWord, tailWord_3364161, baseEnd_3364161] using wordTrace_append hprefix tailTrace_3364161
  have hstable : (prefixWord ++ tailWord_3364161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364161).length < 2 ^ (prefixWord ++ tailWord_3364161).sum := by decide
  have hdescent : baseEnd_3364161 < baseStart_3364161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364166 : List Nat := [6, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_3364166 : Nat := 118140960795 + 3364166 * 2 ^ 59
def prefixEnd_3364166 : Nat := 4983230072969 + 3 ^ 40 * 3364166 * 2
def baseEnd_3364166 : Nat := 1727434159513589918753489

theorem tailTrace_3364166 : CollatzResearch.WordTrace tailWord_3364166 prefixEnd_3364166 1727434159513589918753489 := by
  unfold tailWord_3364166
  simp only [CollatzResearch.WordTrace]
  refine ⟨3834412947819019082979511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 81800809553472407103562901 3834412947819019082979511)
  ·
    refine ⟨5751619421728528624469267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3834412947819019082979511 5751619421728528624469267)
    ·
      refine ⟨8627429132592792936703901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5751619421728528624469267 8627429132592792936703901)
      ·
        refine ⟨3235285924722297351263963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8627429132592792936703901 3235285924722297351263963)
        ·
          refine ⟨4852928887083446026895945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3235285924722297351263963 4852928887083446026895945)
          ·
            refine ⟨3639696665312584520171959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4852928887083446026895945 3639696665312584520171959)
            ·
              refine ⟨5459544997968876780257939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639696665312584520171959 5459544997968876780257939)
              ·
                refine ⟨8189317496953315170386909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459544997968876780257939 8189317496953315170386909)
                ·
                  refine ⟨3070994061357493188895091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8189317496953315170386909 3070994061357493188895091)
                  ·
                    refine ⟨4606491092036239783342637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3070994061357493188895091 4606491092036239783342637)
                    ·
                      refine ⟨1727434159513589918753489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4606491092036239783342637 1727434159513589918753489)
                      ·
                        rfl

theorem cell23_3364166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_3364166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364166 prefixEnd_3364166 := by exact prefixLift 3364166
  have htrace : WordTrace (prefixWord ++ tailWord_3364166) baseStart_3364166 baseEnd_3364166 := by
    simpa [prefixWord, tailWord_3364166, baseEnd_3364166] using wordTrace_append hprefix tailTrace_3364166
  have hstable : (prefixWord ++ tailWord_3364166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364166).length < 2 ^ (prefixWord ++ tailWord_3364166).sum := by decide
  have hdescent : baseEnd_3364166 < baseStart_3364166 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3364172 : List Nat := [2, 2, 1, 3, 2, 4, 1, 1, 3, 2, 2]
def baseStart_3364172 : Nat := 118140960795 + 3364172 * 2 ^ 59
def prefixEnd_3364172 : Nat := 4983230072969 + 3 ^ 40 * 3364172 * 2
def baseEnd_3364172 : Nat := 1727437240397516895278461

theorem tailTrace_3364172 : CollatzResearch.WordTrace tailWord_3364172 prefixEnd_3364172 1727437240397516895278461 := by
  unfold tailWord_3364172
  simp only [CollatzResearch.WordTrace]
  refine ⟨61350716584093436840031385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81800955445457915786708513 61350716584093436840031385)
  ·
    refine ⟨46013037438070077630023539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61350716584093436840031385 46013037438070077630023539)
    ·
      refine ⟨69019556157105116445035309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46013037438070077630023539 69019556157105116445035309)
      ·
        refine ⟨25882333558914418666888241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69019556157105116445035309 25882333558914418666888241)
        ·
          refine ⟨19411750169185814000166181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25882333558914418666888241 19411750169185814000166181)
          ·
            refine ⟨3639703156722340125031159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19411750169185814000166181 3639703156722340125031159)
            ·
              refine ⟨5459554735083510187546739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639703156722340125031159 5459554735083510187546739)
              ·
                refine ⟨8189332102625265281320109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5459554735083510187546739 8189332102625265281320109)
                ·
                  refine ⟨3070999538484474480495041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8189332102625265281320109 3070999538484474480495041)
                  ·
                    refine ⟨2303249653863355860371281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3070999538484474480495041 2303249653863355860371281)
                    ·
                      refine ⟨1727437240397516895278461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2303249653863355860371281 1727437240397516895278461)
                      ·
                        rfl

theorem cell23_3364172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_3364172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3364172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3364172 prefixEnd_3364172 := by exact prefixLift 3364172
  have htrace : WordTrace (prefixWord ++ tailWord_3364172) baseStart_3364172 baseEnd_3364172 := by
    simpa [prefixWord, tailWord_3364172, baseEnd_3364172] using wordTrace_append hprefix tailTrace_3364172
  have hstable : (prefixWord ++ tailWord_3364172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3364172).length < 2 ^ (prefixWord ++ tailWord_3364172).sum := by decide
  have hdescent : baseEnd_3364172 < baseStart_3364172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3364172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
